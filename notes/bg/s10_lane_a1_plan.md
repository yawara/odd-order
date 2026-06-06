# Lane A1 (S10_LocalLemmas) 実行プラン (2026-06-07)

worktree `/home/ywr/odd-order-bg-s10-leaves`, branch `bg-s10-leaves`, `ODD_ISSUE_BASE=2000`。
対象 = `OddOrder/BG/Ch3_MaximalSubgroups/S10_LocalLemmas.lean` の 7 sorry。

## 進捗 (2026-06-07)

- ✅ **10.11(d) `sigma_complement_commutator_cyclic_normal` DONE** (commit `eb6cc10`)。
  sorry-free・full build green (3586 jobs)。axiom 依存 = `propext/Classical.choice/Quot.sound` +
  `sorryAx`(後者は **10.11(c) `sigma_complement_rank_le_one` の transitive 依存のみ**;
  (d) は (c)+Thm 3.7 への正当な還元で、(c) が landing すれば自動 discharge)。
  - レシピ全 6 step を原文 (book p.78, mmd L2856) どおり: ①Isaacs Ch05 `fitting_coprime_abelian_decomp`
    で `K=C_K(P)×[K,P]` ②③積分解 (`coe_mul_of_left_le_normalizer_right` + `K₀⊓Mσ=⊥` の一意性) で
    `P` の FPF ④BG Thm 3.7 (`S03c.isNilpotent_of_normalizing_primeOrder_fixedPointFree`) で
    `K₀⊔Mσ` nilpotent ⑤新ヘルパ `commute_of_coprime_orderOf_of_isNilpotent`
    (`Sylow.directProductOfNormal` で成分分解) で `K₀≤C(Mσ)` ⑥(c) cite + cyclic 一意性。
  - 追加した private ヘルパ 3 個: `commute_of_coprime_orderOf_of_isNilpotent`,
    `cyclic_subgroup_eq_of_card_eq` (S10_BetaRadical の private 複製 → lane 合流時に
    S10_HallStructure へ hoist 推奨), `conjSmul_eq_map`。

- ⚠ **PDF offset 校正完了: `book page = PDF page − 13`** (PDF 102–105 = book 89–92 で確認)。
  当初プランの「10.12 = book p.92」「10.3/10.4/10.5 = p.87」は **誤り** (book p.85–92 は §12
  "The Subgroup E"; 10.3/10.4/10.5 は §10 内なのでもっと前)。正しい §10 範囲:
  - §10 = **book 76–79 = PDF 89–92**, §11 = book 80–84, §12 = book 85–92。
  - **Lemma 10.12: 文 = book p.78 (PDF 91 末), 証明 = book p.79 (PDF 92 冒頭)。**
  - **Lemma 10.13: book p.79–80 (PDF 92–93), 証明あり (mmd で欠落していた本体)。**
  - 10.3/10.4/10.5 は §10 前半 (book p.76 以前 = PDF 88 以前) を要再読込で位置確定。

### 10.12 `disjoint_of_not_conj` 証明 (book p.79 冒頭, PDF 92 で回収)

> Proof. Suppose `p ∈ σ(M) ∩ σ(H)`. Then some Sylow `p`-subgroup `S` of `G` lies in `M`
> and in some conjugate `H^g` of `H`. By the **Uniqueness Theorem**, `r(S) ≤ 2` because
> `H^g ≠ M`. Furthermore `S` is not abelian because `N_G(S) ⊆ M` and `M_σ` is not nilpotent.
> Now we are done because `π(M_α ∩ H_σ) ⊆ α(M) ∩ σ(H) ⊆ σ(M) ∩ σ(H)` and
> `π(M_σ ∩ H_σ) ⊆ σ(M) ∩ σ(H)`.

- 構造: (a)(b) とも「素数集合の disjoint」を背理法 (∃ p∈σ(M)∩σ(H) → S を共通 Sylow に取り
  Uniqueness で矛盾) で示し、subgroup の disjoint (`M_α∩H_σ=1` 等) は `π(A∩B) ⊆ …` の包含から導く。
- **依存**: §9 Uniqueness Thm の「非共役 2 極大に共通する `S` の rank ≤ 2」形 (repo に
  `S09_*` で証明済か要確認), `sigma`/`alpha` 定義の `N_G(Sylow)⊆M` 性, `π(A⊓B)⊆π(A)∩π(B)`,
  「`p∈σ` ⇔ ある Sylow `p` で `N_G⊆M`」のAPI。**中規模だが原文が terse で行間多い**;
  次セッションは上記回収文 + `S09_Uniqueness` の API を突き合わせて形式化する。

## ⚠ 依存の実態 (BG 原文を読んで判明 — 当初の docstring ベース map は楽観的すぎた)

| leaf | BG# | 実依存 | A1 で独立に可? |
|---|---|---|---|
| `sigma_complement_rank_le_one` | 10.11(a)(b)(c) | (a) Thm 4.20+base; **(b) Prop 10.10 (spine!)**; (c)←(b) | ✗ (b)(c) が spine 待ち |
| `sigma_complement_commutator_cyclic_normal` | 10.11(d) | **Thm 3.7** + (c) + coprime 分解 | ✅ **DONE** (eb6cc10, (c) 還元) |
| `disjoint_of_not_conj` | 10.12 | Uniqueness Thm (§9, 証明済) | 証明回収済 (book p.79=PDF 92, 上記参照) |
| `centralizer_isUniquelyMaximal_of_two_le_rank` | 10.3 | Uniqueness | 要 PDF 再読込 (§10 前半, ≈book p.76 以前=PDF≤88) |
| `pRank_eq_two_of_normalizer_le` | 10.5 | §7 Prop 7.5 等 | 要 PDF 再読込 (§10 前半) |
| `alpha_criterion` | 10.4(a)(c) | (a) def+§4; (c) Thm 5.3/ideal | 要 PDF 再読込 (§10 前半) |
| `nonabelian_pSubgroup_rankTwo_elemAbelian_structure` | 10.13 | p-群構造 | 証明回収済 (book p.79–80=PDF 92–93) |

**教訓**: §10 leaf は spine (Prop 10.10/Cor 10.7) と絡む or 旧 MISSING_PAGE (PDF 回収で解決)。
当初の「6-7 完全独立」+「page 番号」推定は誤り。正しい offset = `book = PDF − 13`。

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
