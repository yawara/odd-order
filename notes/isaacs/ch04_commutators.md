# Isaacs Ch.4: Commutators — mini-roadmap

**スコープ**: Isaacs, *Finite Group Theory* (AMS GSM 92, 2008) Ch.4 (pp. 113-146) — 交換子部分群と下降中心列, three-subgroups lemma, Mann の定理, 自己準同型作用での `[G,A]`, 互素作用の Fitting 分解, Thompson P×Q lemma, Baer trick。
形式化先 (予定): [`OddOrder/Isaacs/Ch04_Commutators.lean`](../../OddOrder/Isaacs/Ch04_Commutators.lean) (未着手)。
原典抽出: `references/isaacs/finite-group-theory.mmd` lines 2124-2798。

## 進捗 (2026-05-23 更新)

§4A 部分完成 + §4B Cor 4.10, **Thm 4.11** 完成:

| # | 状態 | 実装 |
|---|---|---|
| **Lem 4.1** (H, K normalize ⁅H,K⁆, 一般版) | ✅ | `subgroup_le_normalizer_commutator_self` + `_right`. Identity `g·⁅a,b⁆·g⁻¹ = ⁅ga,b⁆·⁅b,g⁆` (`conj_commutator_split`) + `closure_induction`. |
| Lem 4.2 (map_commutator) | ✅ mathlib direct | no-wrapper. |
| **Lem 4.3** (⁅H,K⁆ ≤ H ↔ K ≤ N(H)) | ✅ | `commutator_le_iff_le_normalizer` (3 forms: forward/backward/iff). Element identity `k·x·k⁻¹ = ⁅k,x⁆·x`. |
| **Lem 4.4** (class 2 + exponent) | ✅ (2026-05-23) | `pow_mem_center_of_class_le_two_of_commutator_pow` (一般化 statement: 任意 `n`, `commutator G ≤ Z(G)` + 全交換子の `n`乗 = 1 ⇒ `x^n ∈ Z(G)`. Isaacs は `p`-群 + `n = p^e` に特殊化). + `isElementaryAbelian_quotient_center_of_class_le_two` ("In particular" `p`-elem abelian 帰結). class ≤ 2 で `⁅·, z⁆` 左 hom (`commutatorElement_mul_left_of_class_le_two`) + `⁅x^n, z⁆ = ⁅x, z⁆^n` (`commutatorElement_pow_left_of_class_le_two`) 経由. ~80 LOC. "thus Φ(P) ⊆ Z(P)" は Lem 4.5 経由のため別途. |
| Lem 4.5 (P/N elementary abelian iff Φ ⊆ N) | docstring | mathlib `Subgroup.frattini` 経由保留. 必要 helper: "max subgroup of p-group has prime index p" (mathlib 未, ~50 LOC). 下流引用: Lem 4.4 "thus Φ ⊆ Z(P)" 帰結のみ (FT 経路無し). |
| **Lem 4.6** ⭐ (G' = ⁅A, ⊤⁆) | ✅ (2026-05-23) | `commutator_eq_commutator_of_normal_abelian_cyclic_quotient`. mathlib `commutative_of_cyclic_center_quotient` 経由 5-step proof: ⁅A,⊤⁆ ≤ A, lift Q→G/A, ker ⊆ Z(Q) (∵ ⁅a,g⁆∈⁅A,⊤⁆), Q abelian, commutator G ⊆ ⁅A,⊤⁆. Lem 4.6 後半 G' ≅ A/(A∩Z(G)) は別途. |
| Thm 4.7 (maximal class) | docstring | Lem 4.6 後半 (cardinality / isomorphism) + Thm 1.19 (P' ∩ Z(P) 非自明) 経由. ~150-200 LOC. Ch.10 で 2 引用. |
| **Thm 4.8(a)(b)** ⭐ (p>2 class≤2) | ✅ (2026-05-23) | (a) `setOfPowEqOne hC hp : Subgroup G` — `{x : G | x^p = 1}` が部分群 (`p` odd + class ≤ 2). (b) `powPHom hC hp hcomp : G →* G` — `x ↦ x^p` is hom (全交換子 `p`乗 = 1 の仮定下). 核補題 `mul_pow_of_class_le_two`: **commutator collection formula** `(xy)^n = x^n · y^n · ⁅y, x⁆^(n(n-1)/2)`. ~160 LOC (formula 90 + (a) 30 + (b) 25 + helpers). 鍵: `y · x = x · y · ⁅y, x⁆` (`mul_comm_commutator_of_class_le_two`), `y^k · x = x · y^k · ⁅y, x⁆^k` (`pow_mul_eq_mul_pow_commutator_pow_of_class_le_two`). Ch.10 で 2 引用; Baer trick (Lem 4.37) の前身. |
| **Cor 4.10** (Three-sub mod N) | ✅ | `commutator_commutator_le_of_rotate`. 商写像 G→G/N で push し mathlib `commutator_commutator_eq_bot_of_rotate` 適用. |
| **Thm 4.11** ⭐ (lcs additivity) | ✅ (2026-05-23) | `commutator_lowerCentralSeries_le`: `⁅lcs i, lcs j⁆ ≤ lcs (i+j+1)`. `j`-induction (`i` free), step は Cor 4.10 を `H₁=lcs j, H₂=⊤, H₃=lcs i, N=lcs (i+j+2)` で適用. h1: `⁅⊤, lcs i⁆ = lcs (i+1)` 経由で IH at `(i+1)`. h2: IH + commutator_mono + lcs_succ 定義. mathlib `Characteristic (lcs n)` instance が `[N.Normal]` を自動提供. ~30 LOC. |
| **Cor 4.12** (weight n commutator ⊆ G^n) | ✅ (2026-05-23) | `iterLeftCommutator g [g₁,...,gₙ] ∈ lcs G n`. `iterLeftCommutator` を `List.foldl ⁅·, ·⁆` で定義し, 汎用補題 `iterLeftCommutator_mem_lowerCentralSeries_add (n acc) (hacc : acc ∈ lcs n) (gs)` を gs-induction で証明: step は `⁅acc, g⁆ ∈ ⁅lcs n, ⊤⁆ = lcs (n+1)` (mathlib `commutator_mem_commutator` + `lowerCentralSeries` 定義式). 主結果は `n = 0, acc ∈ ⊤ = lcs 0` で specialize. |
| **Cor 4.13** (derived ⊆ lcs exponential) | ✅ (2026-05-23) | `derivedSeries_le_lowerCentralSeries_two_pow_sub_one`: `derivedSeries G r ≤ lcs G (2^r - 1)`. mathlib 既存 `derived_le_lower_central` (`derived r ≤ lcs r`) より strictly stronger (r ≥ 2 で lcs antitone). 証明: `r`-induction + `derivedSeries_succ` + commutator_mono + **Thm 4.11** + 算術 (`pow_succ` + omega + `Nat.one_le_two_pow`). ~10 LOC. |

§4A **大部分完成** (Lem 4.1, 4.3, 4.4, 4.6 前半, **Thm 4.8(a)(b) + collection formula**). 残: Lem 4.5 (Frattini 経由), Lem 4.6 後半 (G' ≅ A/(A∩Z) 同型) → Thm 4.7 (maximal class p-群構造).

§4B **コア部分完成** (Lem 4.9 mathlib, Cor 4.10, Thm 4.11, Cor 4.12, Cor 4.13). 残: Mann (4.14-4.19) — Phase 1 skip 可 (audit で BG/Peterfalvi 直接被引用 0 件確認済).

§4D **`actionCommutator` 定義 + A-不変性 + G-Normal 完成** (2026-05-23): `[G, A]_φ` 記号の自然な実装.
- `actionCommutator φ := Subgroup.closure {g * (φ a) g⁻¹ | g a}`. `Γ = G ⋊[φ] A` 内で
  `⁅inl(G), inr(A)⁆` を `inl` 経由で pull back したもの (∵ `[inl(g), inr(a)] = inl(g * (φ a) g⁻¹)`).
- `actionCommutator_one_eq_bot`: 自明作用 `φ = 1` ⇒ `[G, 1] = ⊥` (@[simp]).
- **`IsAInvariant.actionCommutator`**: `actionCommutator φ` は φ 作用下で A-不変.
  proof: generator `g * (φ a) g⁻¹` → `(φ b) g * (φ (b·a·b⁻¹)) ((φ b) g)⁻¹` (key 計算)
  で生成集合自体が `(φ b)`-stable. `IsAInvariant.closure_of_invariant_set` で結論. ~30 LOC.
- **`actionCommutator.normal`** ⭐: G で normal subgroup (Isaacs §4C 冒頭注).
  generator level conjugation では証明不可 (`(φ a)` 内部 conj が φ 像にない可能性) — Γ 経路:
  1. `actionCommutator_map_inl`: `(actionCommutator φ).map inl = ⁅inl.range, inr.range⁆`
     (~15 LOC, 両側 closure 形に展開 + `SemidirectProduct.commutator_inl_inr` 生成元対応).
  2. **§4A 新規** `commutator_normal_of_sup_eq_top` (Lem 4.1 系): `H ⊔ K = ⊤` ⇒ `⁅H, K⁆.Normal`.
     Lem 4.1 + symmetric の sup から normalizer = ⊤. ~6 LOC.
  3. `Subgroup.Normal.of_map_injective` (mathlib) + `inl injective` で pull back. ~5 LOC.
- 関連 helpers (OddOrder.Mathlib.SemidirectProduct):
  `inl_range_sup_inr_range_eq_top` (`inl_left_mul_inr_right` 経由),
  `commutator_inl_inr` (ext + simp).
- Lem 4.20 (smallest A-inv normal subgroup with G/N trivial action) の前提整備完了.

§4D **Lemma 4.32 完成** (2026-05-23 ⭐, ralph-loop): P p-群 が G 非自明 p-群 に作用 ⇒ `⁅G,P⁆ < G` + `C_G(P) > 1`.
- **前半** `commutator_inl_inr_lt_inl_of_pgroup_action`: Γ = G ⋊[φ] P 内で ⁅inl(G), inr(P)⁆ < inl(G).
  proof: Γ は p-群 (`IsPGroup.semidirectProduct`) で nilpotent. inl(G) 正規 + nontrivial.
  `commutator_lt_self_of_isNilpotent_ambient` 適用. ~10 LOC.
- **後半** `fixedPoints_ne_bot_of_pgroup_action_pgroup`: `Subgroup.fixedPointsOfMulAut φ ≠ ⊥`.
  proof: `MulAction.compHom` で P が G に作用. 1 は trivial fixed point. p ∣ |G| (G nontrivial p-群).
  mathlib `IsPGroup.exists_fixed_point_of_prime_dvd_card_of_fixed_point` で別 fixed point. ~15 LOC.
- 関連 helper: `OddOrder.Mathlib.SemidirectProduct.{finite, IsPGroup.semidirectProduct,
  IsNilpotent.semidirectProduct_of_pGroup}`, `OddOrder.Mathlib.Subgroup.fixedPointsOfMulAut`,
  Ch.4 `iterCommutator_{le_lowerCentralSeries, eq_bot_of_isNilpotent_ambient}` (E ≤ F 不要版),
  `commutator_lt_self_of_isNilpotent_ambient` (strict 降下).

§4B **iterCommutator + Z(F(G)) absorbs G-minimal 補題 完成** (2026-05-23): Lucchini K=⊥ aux 解消の核補題.
- `iterCommutator E F : ℕ → Subgroup G` 定義 + 5 補助補題 (`_le_lowerCentralSeries_map`, `_normal`, `_succ_le_self`, `_le_self`, `_eq_bot_of_isNilpotent`).
- `le_centralizer_of_isMinimalNormal`: E ⊴ G minimal normal + E ≤ F + F ⊴ G + F 冪零 ⇒ E ≤ centralizer F. ~30 LOC. 証明は iterCommutator 降下列 + `Nat.find` で smallest k 取得 + minimality descent.

§4C `[G,A]` 全 8 結果, §4D FT-critical (4.28-4.36, BG Prop 1.6 cluster) が次の主戦場.

前提は Ch.3 (特に Cor 3.28 coprime quotient, Lemma 3.21 Hall-Higman 1.2.3) と Ch.1 (Frattini, nilpotency)。

## mmd 抽出失敗の整理

Ch.3 と違って **MISSING_PAGE marker は 0**, しかし nougat が `4A` `4B` `4C` `4D` の subsection ヘッダを完全に剥がしている:

| § | 実際の境界 (mmd 行) | 内容 |
|---|---|---|
| 4A | 2124-2290 (Problems 2291-2364) | Lemmas 4.1-4.3, 下降中心列定義, Lemmas 4.4-4.5, Lemma 4.6 + Thm 4.7, exponent + Thm 4.8 |
| 4B | 2365-2474 (Problems 2475-2485) | Hall-Witt + three-subgroups (4.9, 4.10), Thm 4.11, Cor 4.12-4.13, Mann (4.14-4.19) |
| 4C | 2486-2587 (Problems 2588-2599) | A acts via aut.: 4.20, 4.21, Thm 4.22, Cor 4.23, Thm 4.24, Lem 4.25, Thm 4.26-4.27 |
| 4D | 2600-2756 (Problems 2758-2793) | Coprime: 4.28, 4.29, 4.30, Thompson PxQ (4.31, 4.32), Thm 4.33 (p-local), Fitting (4.34), 4.35, **4.36 (p odd)**, Baer trick (4.37), Thm 4.38 |

mmd では `**4.22.**` のような頭の太字に `**Theorem**` ラベルが欠落する箇所が 4.22, 4.28, 4.29, 4.30 で見られた (本文ベースの「Lemma」「Theorem」「Corollary」区別は PDF 確認した)。

## 章のセクション分割と全 38 結果

Ch.4 は **§ 4A–4D の 4 節構成** (Ch.2/Ch.3 と同様 subsection には番号のみ・タイトル無し)。

| § | 書籍 pp. | 内容 | Isaacs 番号 | 主要結果 |
|---|---|---|---|---|
| 4A | 113-122 | 交換子の基礎 + 下降中心列 + maximal class p-群 + Ω_r | 4.1 – 4.8 | Lemma 4.6 (cyclic商↔G'), Thm 4.7 (\|A∩Z\|=p ⇒ class=m), Thm 4.8 (p odd, class≤2 ⇒ {x^p=1} 部分群) |
| 4B | 122-131 | Hall-Witt + three-subgroups lemma + Mann | 4.9 – 4.19 | **Lemma 4.9 (three-subgroups)**, Thm 4.11 (G^i G^j ⊆ G^{i+j}), Cor 4.13 (derived length ≤ 1+log₂ m), Mann (4.14, 4.15, 4.19) |
| 4C | 131-138 | A acts on G via automorphisms, [G,A] characterization | 4.20 – 4.27 | Lemma 4.20 (smallest A-inv N), Cor 4.21 ([G,A]=cosets A-inv), Thm 4.22 (faithful ⇒ solvable, derived length ≤ m-1), **Thm 4.24** (faithful ⇒ A nilpotent), **Thm 4.27** ([G,A] nilpotent) |
| 4D | 138-146 | Coprime action: Fitting decomposition + Thompson PxQ + Baer trick | 4.28 – 4.38 | **Lem 4.28 (G=C[G,A])**, **Lem 4.29 ([G,A,A]=[G,A])**, **Cor 4.30** (\|A\| 素因子 ⊂ \|G\| 素因子), **Thm 4.31 (Thompson P×Q)**, **Thm 4.33** (O_{p'}(H) ⊆ O_{p'}(G) for p-local), **Thm 4.34 (Fitting)**, **Cor 4.35** (abelian + Ω₁ fixed ⇒ trivial), **Thm 4.36** (p odd + Ω₁ fixed ⇒ trivial), **Lemma 4.37 (Baer trick)**, **Thm 4.38** (PxQ 強化 p odd) |

### 全結果一覧 (mmd 行番号付き)

#### § 4A — Commutator basics, lower central series, p-group structure (2124-2290)

| # | 種別 | 内容 | mmd |
|---|---|---|---|
| 4.1 | Lemma | `[H,K] ⊴ ⟨H,K⟩` (H, K が `[H,K]` を正規化) | L2128 |
| 4.2 | Lemma | quotient での交換子: `[H,K] mod N = [H̄, K̄]` | L2138 |
| 4.3 | Lemma | `K ⊆ N_G(H) ⟺ [H,K] ⊆ H` (特に `H⊴G ⟺ [H,G] ⊆ H`) | L2144 |
| 4.4 | Lemma | class 2 の p-群: `P'` の exponent `p^e` ⇒ `P/Z(P)` の exponent も `p^e` | L2192 |
| 4.5 | Lemma | `P/N` elementary abelian ⟺ `Φ(P) ⊆ N` (本書 1B の正式証明) | L2196 |
| 4.6 | Lemma | A ⊴ G abelian + G/A cyclic ⇒ `G' = [A,G] ≅ A/(A∩Z(G))` | L2206 |
| 4.7 | Theorem | A ⊴ P abelian, P/A cyclic, \|A∩Z(P)\|=p ⇒ P の nilpotence class = m | L2226 |
| 4.8 | Theorem | p>2, class≤2: (a) `{x ∈ P : x^p=1}` 部分群; (b) commutator 全て `p` 乗 1 ⇒ `x↦x^p` 準同型 | L2280 |

**§4A 補足**: `G^k = [G^{k-1}, G]` (下降中心列) と `G^∞` (有限群での安定値, nilpotent residual) の定義はこの section の本文中 (L2174-2190)。`Ω_r(P) = ⟨x : x^{p^r}=1⟩` 定義も L2246。`maximal class` 定義は L2242。

#### § 4B — Three-subgroups lemma + Mann (2365-2474)

| # | 種別 | 内容 | mmd |
|---|---|---|---|
| 4.9 | Lemma | **Three-subgroups lemma**: `[X,Y,Z]=1, [Y,Z,X]=1 ⇒ [Z,X,Y]=1` | L2379 |
| 4.10 | Corollary | mod N 版: `[X,Y,Z], [Y,Z,X] ⊆ N ⇒ [Z,X,Y] ⊆ N` | L2385 |
| 4.11 | Theorem | `[G^i, G^j] ⊆ G^{i+j}` (下降中心列の和性) | L2395 |
| 4.12 | Corollary | weight n の任意の交換子 ⊆ `G^n` (左結合が最大) | L2417 |
| 4.13 | Corollary | `G^{(r)} ⊆ G^{2^r}` (derived ⊆ lower central, 二進指数). nilpotent class m ⇒ derived length ≤ 1+log₂(m) | L2423 |
| 4.14 | Theorem (Mann) | G nilpotent ⇒ `M(G)` (smallest 2 class sizes generated) は nilpotent class ≤ 3 | L2437 |
| 4.15 | Theorem | G に self-centralizing normal abelian subgroup ⇒ M(G) nilpotent class ≤ 3 | L2441 |
| 4.16 | Lemma | nilpotent ⇒ maximal abelian normal は self-centralizing | L2445 |
| 4.17 | Lemma | K ⊴ G abelian, x noncentral, y=[k,x] ⇒ \|C_G(x)\| < \|C_G(y)\| | L2451 |
| 4.18 | Corollary | K ⊴ G abelian ⇒ `[K, M(G)] ⊆ Z(G)` | L2463 |
| 4.19 | Theorem | 任意有限群: `F = F(M(G))` の nilpotence class ≤ 4 | L2471 |

#### § 4C — A acts on G via automorphisms (2486-2587)

| # | 種別 | 内容 | mmd |
|---|---|---|---|
| 4.20 | Lemma | `[G,A]` は `A` が trivial 作用する最小の A-invariant 正規部分群 | L2500 |
| 4.21 | Corollary | TFAE: (a) 右剰余類すべて A-inv, (b) 左剰余類すべて A-inv, (c) `[G,A] ⊆ H` | L2504 |
| 4.22 | Theorem | `A` faithful, `[G,A,...,A]_m = 1` ⇒ A solvable, derived length ≤ m-1 | L2526 |
| 4.23 | Corollary | m=2 版: `[G,A,A]=1` + faithful ⇒ A abelian | L2544 |
| 4.24 | Theorem | `A` faithful, `[G,A,...,A] = 1` ⇒ A nilpotent | L2550 |
| 4.25 | Lemma | `[G,A,A]=1` ⇒ `[G,A]` abelian (faithfulness不要) | L2566 |
| 4.26 | Theorem | A p-群, G 有限, `[G,A,...,A]=1` ⇒ `[G,A]` は p-群 | L2574 |
| 4.27 | Theorem | A, G 有限, `[G,A,...,A]=1` ⇒ `[G,A]` nilpotent | L2582 |

#### § 4D — Coprime action: Fitting + Thompson P×Q + Baer trick (2600-2756)

| # | 種別 | 内容 | mmd |
|---|---|---|---|
| 4.28 | Lemma | `(|G|,|A|)=1` + (A or G solvable) ⇒ `G = C_G(A)[G,A]` | L2604 |
| 4.29 | Lemma | `(|G|,|A|)=1` ⇒ `[G,A,A] = [G,A]` | L2616 |
| 4.30 | Corollary | A faithful, `[G,A,...,A]=1`, coprime ⇒ \|A\| の各素因子は \|G\| を割る | L2634 |
| 4.31 | Theorem (Thompson) | **P×Q lemma**: A=P×Q (P p-群, Q p'-群) acts on p-群 G, Q fixes every P-fixed element ⇒ Q trivial on G | L2640 |
| 4.32 | Lemma | P p-群, G 非自明 p-群: `[G,P] < G` かつ `C_G(P) > 1` | L2644 |
| 4.33 | Theorem | G p-solvable ⇒ 全 p-local 部分群 H で `O_{p'}(H) ⊆ O_{p'}(G)` | L2654 |
| 4.34 | Theorem (Fitting) | G abelian, coprime ⇒ `G = C_G(A) × [G,A]` | L2664 |
| 4.35 | Corollary | G abelian p-群, A p'-群 が order p 元全部 fix ⇒ A trivial | L2688 |
| 4.36 | Theorem | **p > 2**, G p-群, A p'-群 が order p 元全部 fix ⇒ A trivial | L2694 |
| 4.37 | Lemma (Baer) | G odd order, class ≤ 2 ⇒ `x+y := xy√[y,x]` で加法群構造, (a) 可換なら通常乗法, (b) 加法位数=乗法位数, (c) Aut 保存 | L2698 |
| 4.38 | Theorem | **p > 2**, P p-群 + Q ⊴ A p'-群, Q fixes P-fixed elements ⇒ Q trivial (4.31 強化, P 正規性不要) | L2748 |

## mathlib カバレッジ

`v4.29.1` 時点での Ch.4 関連 API 調査結果。

### ✓ 直接利用できる (mathlib に既存)

| Isaacs | mathlib | ファイル:行 | 備考 |
|---|---|---|---|
| `[H,K]` 部分群版 | `⁅H₁, H₂⁆` / `Subgroup.commutator` | `Commutator/Basic.lean:77, 81` | `commutator_def` |
| `[H,K] ≤ M` ⟺ 生成元判定 | `commutator_le` | `Commutator/Basic.lean:92` | |
| Lemma 4.2 (mod N) | `map_commutator` | `Commutator/Basic.lean:183` | 同型 `f` で `f([H,K]) = [fH, fK]` |
| Lemma 4.3 (`[H,K] ⊆ H ⟺ K ⊆ N(H)`) 部分版 | `commutator_le_right` (H₂.Normal 仮定), `commutator_top_right_le_iff` | `Commutator/Basic.lean:152, 165` | フル等価形は要追加実装 |
| `commute ⟺ [x,y]=1` | `commutatorElement_eq_one_iff_commute` | `Commutator/Basic.lean:40` | |
| `[H,K] = [K,H]` | `commutator_comm` | `Commutator/Basic.lean:129` | |
| `[H₁,H₂] ≤ [K₁,K₂]` mono | `commutator_mono` | `Commutator/Basic.lean:97` | |
| `[H,K] = ⊥ ⟺ H ≤ Z(K)` | `commutator_eq_bot_iff_le_centralizer` | `Commutator/Basic.lean:101` | |
| **Lemma 4.9 three-subgroups** | **`Subgroup.commutator_commutator_eq_bot_of_rotate`** | **`Commutator/Basic.lean:109`** | 完全一致 (`[[H₂,H₃], H₁] = ⊥`, `[[H₃,H₁], H₂] = ⊥ ⇒ [[H₁,H₂], H₃] = ⊥`) |
| 下降中心列 `G^k` | `lowerCentralSeries`, `lowerCentralSeries_succ` | `Nilpotent.lean:299, 316` | 0 は `⊤`, 1 は `commutator G`. **Isaacs と index ズレに注意**: mathlib `lcs 0 = ⊤ = G^1`, `lcs 1 = G' = G^2`, `lcs n = G^{n+1}`. ラッパー時にオフセット要記録 |
| nilpotence class ↔ lcs | `lowerCentralSeries_eq_bot_iff_nilpotencyClass_le` | `Nilpotent.lean:453` | |
| exponent | `Monoid.exponent` | `Exponent.lean:26` | |
| Frattini Φ | `frattini` | `Frattini.lean:24` | |
| `IsSolvable`, `derivedSeries` | 既存 | `Solvable.lean` | Cor 4.13 で利用 |

### △ 部分的にある (拡張要)

| Isaacs | 現状 | 必要拡張 |
|---|---|---|
| Lemma 4.1 (`[H,K] ⊴ ⟨H,K⟩`) | mathlib は H₁.Normal や H₂.Normal を仮定する版のみ (`commutator_normal`) | 一般版 `H, K ≤ N(⁅H,K⁆)` の追加 |
| Lemma 4.3 (`K ⊆ N(H) ⟺ [H,K] ⊆ H`) | `commutator_top_right_le_iff` で `K=⊤` 場合は OK | 任意 K 版の追加 |
| `[xy,z] = [x,z]^y [y,z]` 元レベル恒等式 | `commutatorElement_*` には個別補題のみ; 完全な commutator-expansion lemma は無い | crossed homomorphism 性質として明示化が要る |
| Mann (4.14, 4.15, 4.19), M(G), self-centralizing normal abelian 系 | 存在せず. M(G) は Isaacs 独自集約 | 新規実装. 優先度低 (BG/Peterfalvi で直接引用無し) |

### ✗ 完全に欠落 (新規実装が必要)

順序は重要度・FT クリティカル度:

1. **Lemma 4.28 (`G = C_G(A)[G,A]` for coprime)** — BG Prop 1.6(a) として明示引用. **FT クリティカル**
2. **Lemma 4.29 (`[G,A,A] = [G,A]` for coprime)** — BG Prop 1.6(b). **FT クリティカル**
3. **Theorem 4.34 Fitting decomposition (`G = C_G(A) × [G,A]` for abelian + coprime)** — BG Prop 1.6(d). **FT クリティカル**
4. **Corollary 4.35 (abelian p-群 + p'-A が Ω₁ fix ⇒ trivial)** — BG Prop 1.6(e). **FT クリティカル**
5. **Theorem 4.36 (p>2 一般 p-群版)** — BG Thm 1.11 として明示引用. **FT クリティカル** (BG では Gorenstein 5.3.10 として参照)
6. **Theorem 4.31 Thompson P×Q lemma** — Thompson critical subgroup / ZJ 系の基底道具. BG Thm 1.13 (Thompson critical) の前提で間接利用
7. **Theorem 4.27 ([G,A] nilpotent for chain [G,A,...,A]=1)** — Isaacs 流の "stabilizes series ⇒ A^∞ trivial" の中核. BG Lemma 1.9 と精神同等
8. **Theorem 4.22, 4.24 (faithful chain ⇒ A solvable / nilpotent)** — BG Lemma 1.9 が同精神の弱形
9. **Theorem 4.33 (p-solvable: O_{p'}(H) ⊆ O_{p'}(G) for p-local H)** — Hall-Higman 1.2.3 (= Isaacs Lemma 3.21) を内部使用. BG Cor が同じ系列
10. **Lemma 4.37 Baer trick** — Thm 4.36 / 4.38 の証明ツール. 単体での下流引用は無いが Thm 4.36 とセットで必要
11. **Theorem 4.38 (PxQ 強化, p>2, P 正規不要)** — 4.36 と同じく Baer 経由

### `IsPSolvable` クラスについて

mathlib 4.29.1 に **存在しない**. Ch.4 Thm 4.33 を書くために必要なので、Ch.3 で `IsPiSeparable` を定義する際に併せて `IsPSolvable G p := IsPiSeparable G {p}` 等の定義設計が要る (Ch.3 §3D ノート参照).

## 下流被引用 (Isaacs Ch.5+)

`awk 'NR>=2799' mmd | grep -oE "(Theorem|Lemma|Corollary) 4\.[0-9]+" | sort | uniq -c` の結果:

```
3  Lemma 4.6        ← abelian normal + cyclic 商 (Ch.7, Ch.10) — 注: mmd grep ヒットは出るが Ch.5 5.18 周辺は Problems 5A.5 hint のみで本文の proof 内 cite 無し (2026-05-22 audit 確認)
2  Theorem 4.8      ← class ≤ 2, p > 2 ⇒ x ↦ x^p 準同型 (Ch.5, Ch.10)
2  Theorem 4.7      ← maximal class p-群構造 (Ch.10 × 2)
2  Theorem 4.36     ← p odd, p′-group が order-p 元 fix ⇒ trivial (Ch.5 × 2)
1  Theorem 4.33     ← p-local O_{p′} 押し込み (Ch.10 maximal subgroup 周辺)
1  Lemma 4.29       ← [G,A,A] = [G,A] (Ch.7 J(P) 周辺)
1  Corollary 4.35   ← abelian p-群版 4.36 (Ch.7 周辺)
```

**最も重要 (FT 経路)**:
- **Thm 4.36** は **Isaacs Cor 5.30** ("p odd, 全 order-p 元中心 ⇒ normal p-complement") の証明で **直接利用** (mmd L497 で "It follows by Theorem 4.36 that Q acts trivially on X" と明示). **5.30 は FT 経路で奇数位数仮定との親和性が最大**.
- **Lemma 4.6** が 3 回引用 (Thm 5.18 / Ch.7 / Ch.10) は意外なハブ位置: (abelian normal + cyclic 商) が Sylow 構造解析で頻用.
- **Thm 4.8 (a)** ("x^p = 1 が部分群") は **Ch.10 Thm 10.X** の metacyclic p-群解析で利用 (L2838).
- **Thm 4.33** は Ch.7 (Thompson) や Ch.10 (More Transfer) で p-local 解析に使われる.

Ch.7 (Thompson subgroup, ZJ) が 4.29, 4.35, 4.33 を利用. Ch.10 (More Transfer) が 4.7, 4.8, 4.6 を利用. **Ch.4 全体は Ch.5/6/7/10 でそれなりに引用される**が、Ch.8, Ch.9 は完全独立。

## BG (Bender-Glauberman) での Ch.4 利用

**最も重要な発見**: BG **Proposition 1.6** (BG mmd L416-424) が Isaacs Ch.4 §4D の中核 5 結果をクラスタとして集約:

| BG 1.6 | Isaacs | 内容 |
|---|---|---|
| (a) `G = C_G(A)[G,A] = [G,A]C_G(A)` | **Lemma 4.28** | coprime + solvable |
| (b) `[G,A,A] = [G,A]` | **Lemma 4.29** | coprime |
| (c) `[G,A,A] = 1 ⇒ A acts trivially` | Cor 4.23 系 / Thm 4.22(m=2) | coprime + faithful |
| (d) `G abelian ⇒ G = C_G(A) × [G,A]` | **Theorem 4.34 (Fitting)** | coprime + abelian |
| (e) `G abelian, C_G(A) ⊇ 全素数位数元 ⇒ A trivial` | **Corollary 4.35** | coprime + abelian |

BG はこれらを Gorenstein "Finite Groups" (1968) 5.3.6 (pp. 181), 5.2.3 (p. 177) として引用。**CLAUDE.md の方針通り、Isaacs Ch.4 4.28/4.29/Cor 4.23/4.34/4.35 で代替して形式化する**。

**BG Theorem 1.11** (BG mmd L455) = **Isaacs Theorem 4.36** (p > 2, p-群, p'-A が Ω₁ fix ⇒ trivial). BG が Gorenstein 5.3.10 として引くが、これも Isaacs 4.36 で代替。BG Cor 1.12 がこれを直接利用。

**BG Lemma 1.9** (BG mmd L441) — A が normal series を stabilize + π'-group ⇒ trivial on G. これは Isaacs Theorem 4.22 (faithful chain ⇒ A solvable) / Thm 4.27 ([G,A] nilpotent) と同精神の弱形。BG は独自に短く証明。

**Thompson P×Q (Isaacs 4.31)**: BG mmd で grep 0 件。ただし BG Thm 1.13 (Thompson critical subgroup theorem, BG mmd L461) は P×Q lemma を内部で使う標準的経路 (Gorenstein 5.3.11) を通る。BG 自身は Gorenstein への外部参照で済ます。形式化では Isaacs 4.31 を経由するのが自然。

**Three-subgroups lemma (Isaacs 4.9)**: BG mmd で名前としては 0 件。だが commutator 計算の至るところで暗黙に利用される基本道具。`commutator_commutator_eq_bot_of_rotate` (mathlib) で済む。

## Peterfalvi での Ch.4 利用

Peterfalvi 全 04.* mmd ファイルを grep 結果: **直接引用 0 件**. Three-subgroups, Thompson PxQ, Fitting decomposition, Baer trick, Hall-Witt, `[G,A,A]=[G,A]` のいずれも文字列マッチ無し。Peterfalvi (指標理論) は構造論側の Ch.4 結果を直接使わず、BG/Isaacs 結果を黒箱として依存する設計。

注: Peterfalvi Suzuki 付録 (05.X) や Huppert 付録 (06.0) では Frobenius / 2-transitive permutation group ベースの議論が中心で, Ch.4 を直接引用しない. ただし Suzuki 定理証明の枝で BG §3 (Frobenius actions) を経由するため, 間接的に Isaacs Thm 4.34 / 4.36 が必要となる場面はある.

## 章内依存 (Ch.4 内で 4.X が引用される頻度)

`awk 'NR>=2124 && NR<=2798' mmd | grep -oE "(Theorem|Lemma|Corollary) 4\.[0-9]+" | sort | uniq -c` の結果:

```
最頻 被引用 (証明本文中):
5  Lemma 4.6        — 4.7, 4.8 系 (abelian normal + cyclic 商)
4  Theorem 4.22     — 4.23, 4.24, 4.25-4.27 の入り口 (faithful 作用)
4  Theorem 4.15     — 4.16-4.19 の核 (self-centralizing normal)
4  Lemma 4.2        — bar convention; §4A-§4D 全体で頻用
3  Lemma 4.37       — 4.36, 4.38 の核 (Baer trick)
3  Lemma 4.32       — 4.31, 4.38 の核
3  Lemma 4.3        — normalizer 等価; §4A-§4C 全体
3  Lemma 4.29       — 4.30, 4.31, 4.38 の核
3  Lemma 4.28       — 4.29, 4.30 系の入り口
3  Corollary 4.35   — 4.36, 4.38 の核 (abelian 版 4.36)
2  Theorem 4.36, 4.31, 4.26, 4.14, 4.11, Cor 4.18
```

**章内ハブ**:
- §4A 軸: 4.1 → 4.2 → 4.3 → (4.4 + 4.5) → **4.6** → 4.7 → **4.8**
- §4B 軸: **4.9 (Three Subgroups)** → 4.10 → **4.11** → (4.12, 4.13) → 4.14-4.19 (Mann 系, 独立トピック)
- §4C 軸: 4.20 → 4.21 → **4.22** → (4.23, 4.24, 4.25, 4.26, 4.27)
- §4D 軸: 4.28 → **4.29** → 4.30 → **4.31 (P × Q)** ← 4.32 → 4.33; 別軸 **4.34 (Fitting)** → 4.35 → **4.36** ← **4.37 (Baer)** → 4.38

**Three Subgroups Lemma (4.9)** は §4B 起点で §4C / §4D へ全方向に波及するメタハブ. **Lemma 4.6** が章内最頻 (5 回) で abelian normal + cyclic 商の核ハブ. **Baer trick (4.37)** は §4D で 4.36, 4.38 への核.

## 着手順 (提案)

Ch.1, Ch.2 完了かつ Ch.3 §3E (coprime action) が一通り終わってから着手。Isaacs Ch.4 内部依存と FT クリティカル度から:

1. **§4A 前半 (Lemmas 4.1-4.3)** — mathlib 既存 API のラッパー (一部に generality 拡張). ウォームアップ.
2. **§4A 中盤 (Lemma 4.4-4.6, Thm 4.7)** — class 2 p-群と cyclic 商の構造. `commutator_comm`, Frattini, `Monoid.exponent` を組み合わせる.
3. **§4A 後半 (Thm 4.8, Ω_r 定義)** — `Ω_r(P)` 新規定義. `commutator collection` を class 2 で書く.
4. **§4B (Lemmas 4.9-4.13)** — three-subgroups は mathlib 既存. Thm 4.11 と Cor 4.13 (derived ⊆ lcs) を新規実装. mmd 上は短いが mathlib `lowerCentralSeries` のオフセット (mathlib 0=⊤, Isaacs 1=G) に注意.
5. **§4B 後半 (Mann 4.14-4.19)** — Isaacs 独自集約. 下流引用無し. **後回し可** (Phase 1 内では skip しても問題なし).
6. **§4C (4.20-4.27)** — A が自己準同型作用する場合の `[G,A]` 設計. mathlib に "subgroup of automorphism group acting" の慣用がどう書かれているか先に偵察 (semidirect product 経由が標準?). **設計判断が要る重要 section**.
7. **§4D 前半 (4.28-4.30)** — **FT クリティカル最重要部分**. BG Prop 1.6(a)(b)(c) の中核. 互素作用前提のもとで証明.
8. **§4D 中盤 (Thm 4.31 Thompson P×Q + Lemma 4.32)** — Thompson critical subgroup (Ch.7) と ZJ の前提.
9. **§4D 後半 1 (Thm 4.33)** — Hall-Higman 1.2.3 (Ch.3 Lemma 3.21) 完成後. p-solvable definition 設計を Ch.3 と共有.
10. **§4D 後半 2 (Thm 4.34 Fitting + Cor 4.35)** — BG Prop 1.6(d)(e). **FT クリティカル**.
11. **§4D 終盤 (Thm 4.36 + Lemma 4.37 Baer trick + Thm 4.38)** — BG Thm 1.11 そのもの. Baer trick は odd order 専門なので形式化のスタイル確認 (`Odd (Fintype.card G)` の前提下で `√` を定義).

**FT クリティカル優先**: 4.28, 4.29, 4.34, 4.35, 4.36 > 4.31, 4.27, 4.33 > その他.

## 逆引き: 他章から Ch.4 へ要求される補題

### 2026-05-22: ファイル構造確定 (`notes/meta/forward_dep_policy.md` で文書化)

owner-chapter 規則を採用. Ch.4 dir にサブファイルを作って forward dep を集約:

- **`OddOrder/Isaacs/Ch04_Commutators/ForwardFromCh02.lean`**: Lucchini Thm 2.20 全体
  (本体 theorem + K = ⊥ narrower axiom).
- **`OddOrder/Isaacs/Ch04_Commutators/ForwardFromCh03.lean`**: §3E IsAInvariant 系
  (Thm 3.23 a/b, Lemma 3.24 Glauberman). placeholder 空ファイル.

Ch.4 本体 (4.1-4.38) は将来 `OddOrder/Isaacs/Ch04_Commutators/Main.lean` 等で実装.

### Ch.2 §2D Lucchini Thm 2.20 (K = ⊥ case)

**現状**: Ch.4 dir に full theorem 配置. K > ⊥ branch は Ch.2 内 `lucchini_K_pos_reduction`
(subgroup correspondence のみ使用) を構造補題として呼出. K = ⊥ case のみ
`lucchini_K_bot_aux` (Ch.4 dir 内の narrower axiom) として残置.

**K = ⊥ case が必要とする補題** (Ch.4 領域):

> **Lemma "Z(F(G)) absorbs G-minimal normal in F(G)"**:
> `E ⊴ G`, `E ⊆ F(G)`, `E` minimal normal in `G` ⇒ `E ⊆ Z(F(G))`.

**証明スケッチ** (Isaacs Ch.4 §4A の lcs 経路):

1. `F := F(G)` は冪零 (Ch.1 §1D で完成).
2. `F` の lower central series `F = γ₁(F) ⊇ γ₂(F) ⊇ ...` は ⊥ に到達.
3. `E` を `F` への作用で考え, 降下列 `E ⊇ [E, F] ⊇ [E, F, F] ⊇ ...` を作る.
   各項 `[E, γᵢ(F)]` は `E ⊴ G` + `γᵢ(F) ⊴ G` (characteristic in F, F normal) で `G` で正規.
4. `[[E, F, ..., F]_k] ⊆ E ⊓ γₖ₊₁(F)` (Ch.4 Thm 4.11 系 + 通常 mathlib 系).
   `F` 冪零 で `γₖ₊₁(F) = ⊥` (大きな `k`) なので, 降下列は `⊥` に到達.
5. `E` の minimality より, 降下列の最後の **非自明な** 項 = `E` (途中で ⊥ に飛ぶ前の一つ前).
6. その項は `[E, F]` の繰り返しで, `Z(F)` に含まれる (`[E', F] = ⊥` ⇒ `E' ⊆ Z(F)`).

**Ch.4 のうち何が必要か**:

| 必要要素 | Ch.4 § | 状態 |
|---|---|---|
| `[γᵢ(F), γⱼ(F)] ⊆ γᵢ₊ⱼ(F)` (Thm 4.11) | §4B | 未実装 |
| `E ⊴ G + N ⊴ G ⇒ [E, N] ⊴ G` (Lemma 4.1 系) | §4A | mathlib 部分有 (`commutator_normal`) |
| `commutator_eq_bot_iff_le_centralizer` ⇒ Z(F) 解釈 | mathlib | 既存 |

`[γᵢ(F), γⱼ(F)] ⊆ γᵢ₊ⱼ(F)` (Thm 4.11) は **mathlib に `lowerCentralSeries_succ`** が有るが, 一般の `i + j` 加法性は **新規実装** (~30 行) と思われる. (要確認: `Mathlib.GroupTheory.Nilpotent` での加法性 lemma の有無).

**工数見積もり**: Ch.4 §4A 前半 + §4B Thm 4.11 が完成すれば, この補題自体は ~50-80 行で書ける. 加えて Lucchini K = ⊥ 本体は ~100 行 (minimal normal の選択 + AE 構造 + sub-case 解析). 計 ~150-200 行.

**現実的順序**:

1. Ch.4 §4A (4.1, 4.2, 4.3, 4.4, 4.5, 4.6) — mathlib 既存ラッパー + 拡張.
2. Ch.4 §4B Thm 4.11 (lcs 加法性) — mathlib 既存 + 新規補題 1-2 件.
3. **副産物**: 上記補題 ("Z(F(G)) absorbs G-minimal normal in F(G)") を Ch.4 内 or Ch.2 内 standalone で書く.
4. **Ch.2 Lucchini K = ⊥ 本体** を `lucchini_K_bot_aux` の代わりに書いて axiom 解消.

### Ch.3 §3C hall_C_conjugate (Thm 3.14)

**現状**: axiom 残置. mathlib に Schur-Zassenhaus の **共役性** 部分 (`exists_right_complement'_of_coprime` の存在性のみ) 無し.

**Ch.4 領域からの寄与**: 直接の依存無し. ただし以下が利用可能になれば形式化が楽:

- Ch.4 §4D Thm 4.34 (Fitting decomposition) — abelian coprime での共役性は Fitting 経由で導出可能.

**現実的に直接書くべき**: mathlib に SZ 共役性を新規実装する道 (Ch.4 とは独立) のほうが順序付け良い.

## 未解決の疑問

* **mathlib `lowerCentralSeries` の index 規約と Isaacs `G^k` のズレ** — mathlib は `lcs 0 = ⊤`, `lcs 1 = G' = commutator G`. Isaacs は `G^1 = G`, `G^2 = G' = [G,G]`. ラッパー時のオフセット表記をどう統一するか. 候補: section 冒頭の docstring に "Isaacs `G^k` corresponds to mathlib `lowerCentralSeries (k-1)`" と明示し、新規定義 (`isaacsLcs k := lowerCentralSeries (k-1)`) は作らず docstring のみで吸収.
* **`[G,A]` の設計** — A ⊆ Aut G の場合と semidirect product `G ⋊ A` の場合を統合する mathlib 慣習を要偵察. mathlib の `MulAction G H` や `MulSemiringAction` の延長として `[G,A]` を直接書ける API があれば良い.
* **`IsPSolvable G p` の定義** — Ch.3 で `IsPiSeparable G π` を定義する際に、`IsPSolvable G p := ∀ q, q.Prime → q ≠ p → IsPiSeparable G {q}` などの整合形を要決定. Isaacs では p-solvable は p, p' のみの組成因子 (Isaacs §3D 定義). mathlib API としては `IsSolvable` の汎用化として書くのが自然.
* **Mann 4.14-4.19 を Phase 1 で形式化するか?** — Isaacs/BG/Peterfalvi いずれでも下流引用ゼロ. 形式化価値は教科書完全性のみ. Phase 1 を MVP として進める方針なら **後回し or skip**.
* **Baer trick の `Odd order + class ≤ 2 ⇒ abelian group structure`** — `√` を power 演算で書く形式化スタイル要確認. Mathlib `ZMod` や `Nat.gcd` 系で平方根的演算がどう書かれているか.
* **Thm 4.31 (P×Q lemma) を Ch.4 のどの段階で着手するか** — Ch.7 (Thompson J(P), ZJ) クリティカルパスに乗っているので、§4D 前半 (4.28-4.30) と一緒に先行実装する選択肢あり.

## 関連メモ

- 上流: [`ch01_sylow.md`](ch01_sylow.md), [`ch02_subnormality.md`](ch02_subnormality.md), [`ch03_split.md`](ch03_split.md)
- 下流予定: `ch05_transfer.md` (Lemma 4.6, Thm 4.7, 4.8 を引用), `ch07_thompson.md` (Thm 4.31, 4.33, 4.36 を引用)
- 横断: [`../meta/mathlib_coverage.md`](../meta/mathlib_coverage.md) (mathlib 全体カバレッジ), [`../meta/lean_formalization_tips.md`](../meta/lean_formalization_tips.md) (mathlib gotcha 集)
