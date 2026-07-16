# Isaacs Ch.10: More Transfer Theory — mini-roadmap

> 🚧 **形式化進行中 (lane c, 2026-07-17〜)** — 旧「FT 経路外 deferred」は 2026-07-16 の
> 全 3 冊フェーズ移行で失効。着手順は上流優先+文書順 (§10A → §10B → §10C)。
>
> - ✅ **Lemma 10.3** (a)(b)(c) — `Ch10_MoreTransfer/WreathRecognition.lean` (sorry-free)
> - ✅ **Theorem 10.4** `C_p ≀ C_p` 認識 — 同 leaf,
>   `nonempty_mulEquiv_wreath_of_noncommProd_conjClass_ne_one` (sorry-free)。
>   共役類積は `Finset.noncommProd`、`C_p ≀ C_p` は
>   `Multiplicative (ZMod p) ≀ᵣ Multiplicative (ZMod p)`。
>   mathlib `Sylow.mulEquivIteratedWreathProduct` + 新規橋
>   `iteratedWreathProductTwoMulEquiv` を使用。
>   副産物 (shared): `PRank.lean` に `IsElementaryAbelian.exists_isComplement'`
>   (elementary abelian の任意部分群に補部分群)。
> - ⏭ 次: **Cor 10.5** (準同型像版; P/Z 帰納) → 10.6/10.7 (pretransfer) → …
>
> 以下の本文は 2026-05-23 audit 時点の調査 (被引用 0 等の事実は有効、
> 「skip 推奨」結論のみ失効)。

**スコープ**: Isaacs, *Finite Group Theory* (AMS GSM 92, 2008) Ch.10 (pp. 295-324).
形式化先: `OddOrder/Isaacs/Ch10_MoreTransfer/` (Lemma 10.3 から実装開始済).
原典抽出: `references/isaacs/finite-group-theory.mmd` lines 5310-5914.
ROADMAP 上の位置: **第 5 波 (Ch.6 完了後、Ch.7 と並列)** — Isaacs 本編の最終章. 前提は Ch.4 (Commutators: Thm 4.6, 4.7, 4.8), Ch.5 (Transfer: Thm 5.5, 5.6, Lemma 5.12, Cor 5.22), Ch.6 (Thm 6.11) を軽く参照する程度.
4 視点 framework 適用 (2026-05-23 audit 統合): 詳細クロス参照 [`../meta/ch08_10_audit_2026_05_23.md`](../meta/ch08_10_audit_2026_05_23.md).

## TL;DR — Isaacs 内では葉、BG/Peterfalvi 直接被引用ゼロ、Phase 1 スキップ推奨

**Ch.10 全 28 結果のうち、BG / Peterfalvi 本体 + Suzuki / Huppert 付録への直接被引用は 0 件**:

| Ch.10 概念 | BG 出現 | Peterfalvi 出現 |
|---|---|---|
| Yoshida's theorem (10.1) | 0 | 0 |
| Huppert metacyclic (10.12) | 0 | 0 |
| transitivity of transfer (10.8) | 0 | 0 |
| Mackey transfer (10.10) | 0 | 0 |
| principal ideal / Furtwängler (10.18) | 0 | 0 |
| augmentation ideal Δ(G), Z[G]-module 流transfer (10.19-10.27) | 0 | 0 |
| Alperin-Kuo \|G:G' ∩ Z(G)\| (10.28) | 0 | 0 |

**BG §4 (L1377-1640) には "metacyclic p-group" の話題が**ある (Lemma 4.10 / Proposition 4.11 (Huppert) / Theorem 4.12 (Huppert) / Theorem 4.16 (Blackburn) 等) **が、Isaacs 10.12 とは別の定理**:

- **Isaacs 10.12 (Huppert)**: G 有限, P ∈ Syl_p(G) 非可換 metacyclic, p > 2 ⇒ p ∣ \|G:G'\| (= G が non-simple)
- **BG Proposition 4.11 (Huppert)**: p > 3, R が p-group で \|Ω_1(R)\| ≤ p^2 ⇒ R は metacyclic
- **BG Theorem 4.12 (Huppert)**: p odd, R metacyclic p-group, A が p'-operator ⇒ R abelian

BG が引く Huppert は **Huppert *Endliche Gruppen I* (1967) Satz III.11.6 / III.13.7** であって, Isaacs 10.12 で扱う metacyclic + Yoshida 経路の Huppert (= transfer-theoretic Huppert) とは別系統. 証明戦略も全く別 (BG は Hall regular p-groups + Maschke を直接適用, Isaacs は Yoshida 10.1 + Maschke).

**Peterfalvi 付録 06.0 "A Special Case of a Theorem of Huppert"** も別物: solvable doubly transitive permutation groups に関する Huppert (Huppert-Blackburn Ch.XII §7) で, metacyclic p-group とは無関係.

**結論**: §1G Chermak-Delgado, Ch.9 と同じく **FT 経路では未着手 — Phase 1 スキップ推奨**. Ch.5 §5D (Focal Subgroup) と §5E (Frobenius normal p-complement) で BG/Peterfalvi に必要な transfer 内容は尽きている. Ch.10 は Isaacs 本編を Phase 1 で全部閉じたい場合の "完備化" 仕事になる.

## 視点 1: forward dependencies (2026-05-23 audit 統合)

**(a) Isaacs 内 後続章**: Ch.10 は Isaacs FGT の **最終 main chapter**. Ch.11+ 以降は存在せず, 後続 Isaacs 章への forward edge は本質的に **0 件** (Index と Bibliography のみ; 既存 L154-159 参照).

**(b) BG / Peterfalvi 直接被引用**: 再 grep 結果 (`grep -c` 全 mmd) — `Yoshida` 0, `Mackey` 0, `Furtwängler` / `Furtwangler` 0, `principal ideal` 0, `transitivity.*transfer` 0, `augmentation ideal` 0, `Alperin` 0. `metacyclic` 12 件はすべて **BG §4 別 Huppert (Endliche Gruppen I) の文脈での偽陽性** であり Isaacs Ch.10 §10B 非依存 (詳細 L172-189 と §2.4 共通 subroutine 補足参照). ⇒ FT 経路への直接 forward edge **0**.

**(c) Class field theory への forward edge** (mathlib upstream 視野): Thm 10.18 principal ideal theorem (Furtwängler) ＋ augmentation ideal API (Δ(G), 10.19-10.27) は mathlib `NumberTheory.ClassNumber.*` 系統への upstream 候補. FT 経路で 0 件だが Phase 1 完成後の余剰時間で `Mathlib/GroupTheory/AugmentationIdeal.lean` 単独 PR 価値が HIGH (詳細 §5.4).

**(d) Suzuki / Sz(q) 系 wreath product 共有**: Peterfalvi §05.6 PSU(3,q) appendix でも wreath product 利用予定. mathlib `RegularWreathProduct` を Ch.10 §10A と共有して両方の重複実装を避ける.

## 章のセクション分割と全 28 結果

mmd 抽出では `### 10a` (L5312), `### Problems 10a` (L5553), `### Problems 10B` (L5646), `### 10c` (L5656), `**Problems 10C**` (L5895) が捕捉できている. §10B のヘッダは inline text marker `**10B**` (L5577) で `###` 形式は欠落. MISSING_PAGE marker 無し (Ch.10 mmd 品質は良好):

| § | mmd 行 | 内容 | Isaacs 番号 | 主要結果 |
|---|---|---|---|---|
| 10A | 5312-5552 | Yoshida's theorem + 補助補題 (C_p ≀ C_p の認識・transitivity + Mackey transfer) | 10.1 – 10.11 | **10.1 Yoshida**, 10.2 class < p 系, **10.3, 10.4 wreath product 認識**, **10.8 transitivity of transfer**, **10.10 Mackey transfer**, 10.11 failure of fusion control の lemma |
| 10B | 5553-5645 | Huppert metacyclic Sylow + Maschke | 10.12 – 10.17 | **10.12 Huppert** (nonabelian metacyclic Sylow ⇒ p ∣ \|G:G'\|), 10.13 metacyclic 閉性, 10.14 W not metacyclic image, **10.15 main lemma**, **10.16 Maschke** (一般化), 10.17 elementary abelian + coprime 系 |
| 10C | 5656-5894 | 主要 ideal theorem (Furtwängler) ＋ Z[G]-module 流 transfer 解釈 | 10.18 – 10.28 | **10.18 principal ideal theorem** (transfer to G' は trivial), 10.19-10.23 augmentation ideal API, 10.24 v(G) ≅ Ξ(...), 10.25 \|K:G'\| 倍化, 10.26 commutative ring lemma, 10.27 Lemma, **10.28 Alperin-Kuo** g^{\|G:G'∩Z\|} = 1 |

### § 10A — Yoshida's theorem and wreath product recognition (lines 5312-5552)

§10A の戦略: "P の Sylow normalizer N_G(P) が p-transfer を control しない場合, P は C_p ≀ C_p を準同型像に持つ" (Yoshida 10.1). このため (i) pretransfer の精密計算 (10.6, 10.7), (ii) C_p ≀ C_p の characterisation (10.3, 10.4, 10.5), (iii) 一般 transfer 理論補助 (10.8 transitivity, 10.9 R Φ(S) 条件, 10.10 Mackey), (iv) failure of fusion control の補題 (10.11) を順に組む.

| # | 種別 | 内容 | mmd |
|---|---|---|---|
| 10.1 | Theorem | **Yoshida**: P ∈ Syl_p(G), N = N_G(P). N が p-transfer を control しない ⇒ C_p ≀ C_p は P の準同型像 | L5332 |
| 10.2 | Corollary | nilpotence class(P) < p ⇒ N_G(P) は p-transfer を control する | L5334 |
| 10.3 | Lemma   | P p-群, A ◁ P, \|P:A\|=p, A elementary abelian (order p^t, t≥2), A は P の 1 共役類で生成 ⇒ \|Z(P)\|=p, \|P'\|=p^{t-1}, class(P)=t | L5342 |
| 10.4 | Theorem | P p-群, A ◁ P elementary abelian, \|P:A\|=p, \|Z(P)\|=p, A 内の非中心共役類の積 ≠ 1 ⇒ P ≅ C_p ≀ C_p | L5354 |
| 10.5 | Corollary | P p-群, A ◁ P elementary abelian index p, a ∈ A − Z(P), conjugacy class の積 ≠ 1 ⇒ C_p ≀ C_p は P の準同型像 | L5382 |
| 10.6 | Lemma   | M ◁ P, \|P:M\|=p, V: P → M pretransfer: x ∈ M ⇒ V(x) ≡ ∏ x^t mod M', x ∉ M ⇒ V(x) ≡ x^p mod M' | L5398 |
| 10.7 | Lemma   | M ◁ P, \|P:M\|=p, V(M) ⊄ Φ(M) ⇒ C_p ≀ C_p は P の準同型像 | L5413 |
| 10.8 | Theorem | **Transitivity of transfer**: H ⊆ K ⊆ G, \|G:H\| < ∞, U: G→K, W: K→H, V: G→H pretransfer ⇒ V(g) ≡ W(U(g)) mod H' | L5425 |
| 10.9 | Theorem | S < P p-群, V: P → S pretransfer, R = ⟨ s ∈ S \| o(s) < o(x) ⟩, V(x) ∉ R Φ(S) ⇒ C_p ≀ C_p は P の準同型像 | L5469 |
| 10.10 | Theorem | **Mackey transfer**: X = (H,K)-double cosets の代表系, V: G → H, W_x: K → K ∩ H^x pretransfer ⇒ V(k) ≡ ∏ x W_x(k) x^{-1} mod H' | L5489 |
| 10.11 | Lemma   | P ⊆ N ⊆ G, P ∈ Syl_p(G), N が p-transfer を control しない ⇒ ∃ M ◁ N, \|N:M\|=p, U(G) ⊆ M ∀ pretransfer U: G → N | L5521 |

§10A 末で Yoshida 10.1 を 10.11 + 10.10 + 10.9 で証明する.

### § 10B — Huppert metacyclic + Maschke (lines 5553-5645)

`**10B**` text marker (L5577) で section 開始. Yoshida 10.1 を直接応用して "nonabelian metacyclic Sylow ⇒ p ∣ \|G:G'\|" (Huppert 10.12) を示す. 鍵は (i) W = C_p ≀ C_p は metacyclic 群の準同型像になり得ない (10.14), (ii) Maschke 一般化 (10.16) で normal subgroup を慎重に切り出して帰納構造を組む (10.15).

| # | 種別 | 内容 | mmd |
|---|---|---|---|
| 10.12 | Theorem | **Huppert**: G 有限, P ∈ Syl_p(G), p > 2, P nonabelian + metacyclic ⇒ p ∣ \|G:G'\| | L5579 |
| 10.13 | Lemma   | metacyclic 性は (a) 商, (b) 部分群で保たれる | L5583 |
| 10.14 | Lemma   | p > 2 ⇒ W = C_p ≀ C_p は metacyclic 群の準同型像にならない (W' が elementary abelian rank > 1) | L5590 |
| 10.15 | Theorem | P ◁ N (= P が N の Sylow), P nonabelian + metacyclic, p > 2 ⇒ p ∣ \|N:N'\| (Yoshida + 10.16) | L5596 |
| 10.16 | Theorem | **Maschke (一般化)**: K 有限位数 m, K ↷ V = U × W, U abelian + K-invariant, u ↦ u^m が U 上で全単射 ⇒ ∃ K-invariant N ◁ V, V = U × N | L5600 |
| 10.17 | Corollary | K 有限 ↷ elementary abelian p-群 V, p ∤ \|K\|, U ⊆ V が K-invariant ⇒ ∃ K-invariant N ⊆ V, V = U × N | L5608 |

10.15 の証明では (1) P' を unique normal of order p に圧縮, (2) V = Ω_1(P) を elementary abelian of order p^2 とし, (3) Maschke で V = P' × W に分解, (4) Z = Z(P) で V ⊄ Z を導き矛盾を避ける形で N/P を cyclic factor 群上に作用させる.

### § 10C — Principal ideal theorem (Furtwängler) and Z[G]-module transfer (lines 5656-5894)

`### 10c` (L5656) で section 開始. transfer 写像 G → G'/G'' が常に自明であることを示す古典結果 (= "principal ideal theorem", 数論で class field theory に対応). 証明戦略: (1) augmentation ideal Δ(G) ⊂ Z[G] の基本性質 (10.19, 10.20), (2) K ⊆ G の transfer を Δ(K)Δ(G) modulo の Z[G]-module 構造 (10.21-10.24) で書き換え, (3) 可換環論 (10.26 = Nakayama 型 lemma) で結論 (10.25 → 10.18). Hochschild の議論を踏襲. **Isaacs が本書で唯一 group ring を本格使用する箇所**.

| # | 種別 | 内容 | mmd |
|---|---|---|---|
| 10.18 | Theorem | **Furtwängler / principal ideal theorem**: 有限群 G の transfer v: G → G'/G'' は trivial map | L5660 |
| 10.19 | Lemma   | Δ(G) = augmentation ideal は加法群として {g − 1 \| 1 ≠ g ∈ G} を Z-basis に持つ | L5701 |
| 10.20 | Theorem | G/G' ≅ Δ(G)/Δ(G)^2 (加法群) via G'g ↔ (g − 1) + Δ(G)^2 | L5733 |
| 10.21 | Lemma   | K ⊆ G, T ⊇ {1} 右 transversal, α ∈ Δ(K)Δ(G) ⇒ 各 t-成分 α_t ∈ Δ(K), Σ α_t ∈ Δ(K)^2 | L5747 |
| 10.22 | Corollary | Δ(K)^2 = Δ(K)Δ(G) ∩ Δ(K) = Δ(K)Δ(G) ∩ Z[K] | L5757 |
| 10.23 | Corollary | K ⊆ G, \overline{Δ(G)} = Δ(G)/Δ(K)Δ(G) ⇒ \overline{Δ(K)} ≅ K/K' via \overline{k−1} ↔ K'k | L5763 |
| 10.24 | Theorem | K ◁ G, v: G → K/K' transfer, Ξ: \overline{Δ(G)} → \overline{Δ(G)} = Σ_T t (transversal sum) による左乗法 ⇒ v(G) ≅ Ξ(\overline{Δ(G)}) | L5777 |
| 10.25 | Theorem | G' ⊆ K ⊆ G, v: G → K/K' transfer ⇒ v(g)^{\|K:G'\|} = 1 ∀ g ∈ G | L5813 |
| 10.26 | Theorem | A 左 R-module (R 可換環), U ⊆ R ideal, A・U 加法生成有限, \|A:UA\| = m ⇒ ∃ r ∈ R, rA = 0, r ≡ m·1 mod U (classical adjoint 引数) | L5817 |
| 10.27 | Lemma   | K ◁ G, ε ∈ Z[G] が ε \overline{Δ(G)} = 0, m = δ(ε) ⇒ \|G:K\| ∣ m, (m/\|G:K\|) Ξ = 0 | L5841 |
| 10.28 | Corollary | **Alperin-Kuo**: A = G' ∩ Z(G) ⇒ g^{\|G:A\|} = 1 ∀ g ∈ G (10.18 + Thm 5.6 + 10.8 から導出) | L5891 |

## mathlib カバレッジ

**Ch.10 主要結果のうち mathlib 直接対応はほぼゼロ**. Ch.5 mathlib 資産 (`Transfer.lean`, `Focal.lean`) はあるが Yoshida / Mackey / principal ideal theorem / augmentation-ideal 流 transfer 理論はいずれも未収載.

### 直接利用できるもの

| Isaacs | mathlib | 備考 |
|---|---|---|
| pretransfer (10.6-10.8 の基底) | `MonoidHom.transfer` 周辺 (`Mathlib/GroupTheory/Transfer.lean:148`) ＋ `transferFunction` (`Transfer.lean:89`) | pretransfer に相当する `transferFunction` も実装済 |
| (H,K)-double coset (10.10 の構文) | `DoubleCoset.doubleCoset` (`Mathlib/GroupTheory/DoubleCoset.lean:37`) ＋ `DoubleCoset.quotient` | quotient + disjoint 性は完備 |
| transfer = g ↦ g^n (10.28 の途中) | `MonoidHom.transferCenterPow` (`Transfer.lean:228`) | Ch.5 5.6 のラッパー |
| Maschke (10.16, 10.17) | `Mathlib/RepresentationTheory/Maschke.lean` | char ∤ \|K\| 版. Isaacs の "u ↦ u^m が bijective" は同じ条件の同値表現. ベクトル空間版 (10.17) は直接 |
| augmentation map / ideal | `MonoidAlgebra` 系 ( `Mathlib/Algebra/MonoidAlgebra/Basic.lean` 等) | `MonoidAlgebra.lift` 等は揃うが **augmentation `δ: Z[G] → Z` と Δ(G) は mathlib に未定義** |
| Z[G] = group ring | `MonoidAlgebra Z G` で実装 | 標準形式 |

### 新規実装が必要 (mathlib 未収載)

| Isaacs | 状況 | コスト見積もり |
|---|---|---|
| **`WreathProduct C_p C_p`** | **(2026-05-23 audit 訂正)** mathlib v4.29.1 に `Mathlib/GroupTheory/RegularWreathProduct.lean` (260 行, 2025) 既存: `RegularWreathProduct D Q` (中置 `D ≀ᵣ Q`), `IteratedWreathProduct G n`, `Sylow.mulEquivIteratedWreathProduct` (`:242`) (Sylow `p`-subgroup of `Sym(p^n)` ≅ iterated wreath). `Cp ≀ Cp = (ZMod p) ≀ᵣ (ZMod p)` 直接. ad-hoc 手作りは不要 | **中** (旧評価「大」を訂正; mathlib API 利用) |
| **Lemma 10.3, Thm 10.4, Cor 10.5** (C_p ≀ C_p 認識) | mathlib 未収載. 10.4 の S_{p^2} ↪ argument は permutation embedding (mathlib `Equiv.Perm`) ＋ class size 計算 | 中 (linear algebra over F_p の援用) |
| **Lemma 10.6, 10.7** (pretransfer pth-power 化) | mathlib `transfer_eq_pow` (`Transfer.lean:205`) ＋ Frattini factor `Mathlib/GroupTheory/Frattini` で類似. Isaacs 流ステートメントへ橋渡し | 中 |
| **Thm 10.8 transitivity of transfer** | mathlib **完全未収載** (`grep "transitivity.*transfer"` 0). pretransfer の合成 = pretransfer ということを `transferFunction` ベースで示す | 中 (一般原則だが proof は技術的) |
| **Thm 10.9** (R Φ(S) 条件) | 10.6 + 10.7 + 10.8 の組み合わせ. Isaacs の P-induction を写す | 中 |
| **Thm 10.10 Mackey transfer** | mathlib 未収載 (`DoubleCoset` API ＋ pretransfer で構成可能だが補題化されていない) | **大** (Mackey 公式 transfer 版を 1 ファイルで初実装) |
| **Lemma 10.11** | Ch.5 §5D Focal Subgroup と関連. \|G:A^p(G)\| = \|w(N)\| 経路の補完 | 中 |
| **Thm 10.1 Yoshida** | 10.3 + 10.4 + 10.10 + 10.11 を結合. 章の中核. **mathlib upstream 視野なら大きな貢献** | **大** |
| 10.2 (class < p ⇒ N controls p-transfer) | 10.1 + 10.3 の系 | 短 |
| **Thm 10.12 Huppert metacyclic** | Yoshida + 10.15. mathlib 未収載 | 中 (10.15 経由) |
| `IsMetacyclic G` 定義 | mathlib **未収載** (`grep "Metacyclic\|metacyclic"` 0). `∃ N : Subgroup G, N.IsNormal ∧ IsCyclic N ∧ IsCyclic (G ⧸ N)` で 1 行 def | 短 |
| 10.13, 10.14 metacyclic 閉性 + W ≄ image | 上記 def の上に直接 | 短 |
| **Thm 10.15** | Yoshida 10.1 ＋ Maschke 10.17 ＋ Ω_1(P) 構造分析 (Ch.4 Thm 4.8 が必要) | 中 |
| 10.16 Maschke 一般化版 | mathlib `RepresentationTheory.Maschke` は char-0 / ベクトル空間版. **群作用版** (u ↦ u^m bijective) は新規 | 中 |
| 10.17 Maschke for elementary abelian | 10.16 ベース ＋ mathlib `Module` 互換変換 | 短 |
| **Thm 10.18 principal ideal theorem** | mathlib 完全未収載 (`grep "principal.ideal.*Group\|Furtwangler\|Furtwängler\|Hochschild.*transfer"` 0) | **大** |
| Δ(G) augmentation ideal | mathlib 未収載 (`grep "augmentation\|Augmentation"` 0). `def Δ : Ideal (MonoidAlgebra ℤ G) := (MonoidAlgebra.augmentation).ker` で定義 ＋ Lemma 10.19 が Z-basis 保証 | 中 |
| **Thm 10.20 G/G' ≅ Δ(G)/Δ(G)^2** | mathlib 未収載. Z[G] と G^{ab} の関係 (群コホモロジー H_1 風) で重要だが mathlib に直接対応無し | 中 |
| 10.21-10.23 (Δ(K)Δ(G) と \overline{Δ(K)} の解析) | 未収載. transfer の augmentation 表示の前準備 | 中 |
| **Thm 10.24** v(G) ≅ Ξ(\overline{Δ(G)}) | 未収載. 章の山場 | 中 |
| 10.25 (\|K:G'\|-倍化) | 10.24 + 10.26 + 10.27 | 中 |
| **Thm 10.26 (classical adjoint lemma)** | 可換環論 lemma. mathlib `Matrix.adjugate` (= classical adjoint) ＋ Cayley-Hamilton 経由. 標準 | 中 (mathlib 内で類似 Nakayama 補題あるが Isaacs 流が個別) |
| 10.27 | 10.21 + 10.24 系の組み立て | 中 |
| **Cor 10.28 Alperin-Kuo** | 10.18 + Thm 5.6 + Thm 10.8 の合成 | 短 (10.18 完成後) |

### mathlib カバレッジ概観

| 種別 | 数 | 比率 |
|---|---|---|
| 直接利用可 (Transfer / DoubleCoset / Maschke の基底のみ) | ~3 / 28 | 11% |
| 同等概念有り、構成必要 (pretransfer / transfer_pow / Z[G] / Maschke 補強) | ~5 / 28 | 18% |
| 新規実装が必要 (Yoshida / Mackey / principal ideal / augmentation 周辺) | ~20 / 28 | **71%** |

Ch.10 は **Ch.6 (Frobenius Actions) と並んで Phase 1 で mathlib カバレッジが最も薄い章のひとつ**. しかも FT 経路への直接寄与がほぼゼロ (下記参照) なので, **コスト/効果比は最低**.

## 視点 3: mathlib status — proof-internal API per major theorem (2026-05-23 audit 統合)

上記「## mathlib カバレッジ」は statement-level overview. 以下は **証明本体で呼ぶ mathlib v4.29.1 API** の具体名 + path (audit §3.3 由来):

| Isaacs | mathlib API (v4.29.1, exact paths + names) |
|---|---|
| **10.1 Yoshida** | **修正** (wreath cost 「大→中」): `Mathlib/GroupTheory/RegularWreathProduct.lean` (260 行, 2025): `RegularWreathProduct D Q` (中置 `D ≀ᵣ Q`), `IteratedWreathProduct G n`, **`Sylow.mulEquivIteratedWreathProduct` (`:242`)** が `C_p ≀ C_p` 認識を直接与える. `MonoidHom.transfer` (`Mathlib/GroupTheory/Transfer.lean:148`), `transferFunction` (`:89`), `transferTransversal` (`:111`). + `IsPGroup`, `Subgroup.normalClosure`, `Sylow.Conj` |
| **10.8 transitivity of transfer** | mathlib **完全不在** (`grep "transfer_comp\|transitivity.*transfer"` 0). `MonoidHom.transfer`, `transferFunction`, `transferTransversal` を基底に **新規 lemma `transfer_comp`** を `OddOrder/GroupTheory/TransferMackey.lean` 内に構築. 補助 `Subgroup.commutator`, `QuotientGroup.mk` |
| **10.10 Mackey transfer** | `Mathlib/GroupTheory/DoubleCoset.lean`: `doubleCoset` (`:37`), `Quotient` (`:79`), `quotToDoubleCoset` (`:109`), `disjoint_out` (`:149`), `iUnion_quotToDoubleCoset` (`:155`). + `H.LeftTransversal` (`Transfer.lean:111`). DoubleCoset API がほぼ完備 ⇒ コスト「大 → 中-大」 |
| **10.16 Maschke 一般化** | `Mathlib/RepresentationTheory/Maschke.lean` の `MonoidAlgebra.Submodule.exists_isCompl` (`:162`), `equivariantProjection_condition` (`:123`) は **module 版**. Isaacs 10.16 は群作用版 (`u ↦ u^m` bijective hypothesis) で mathlib 直接対応無し ⇒ `OddOrder/GroupTheory/MaschkeGroupAction.lean` 新規 |
| **10.18 principal ideal** | **augmentation NOT in mathlib** (`grep "augmentation\|Augment" .lake/.../MonoidAlgebra/` 0 件). 自前: `def augmentation : MonoidAlgebra ℤ G →+* ℤ := MonoidAlgebra.lift ℤ G ℤ (fun _ => 1)` (mathlib `MonoidAlgebra/Basic.lean:220`). + `def Δ : Ideal (MonoidAlgebra ℤ G) := (augmentation G).ker`, `Ideal.span_singleton`, `Ideal.Quotient` |
| **10.26 classical adjoint** | `Mathlib/LinearAlgebra/Matrix/Adjugate.lean`: `Matrix.adjugate` (`:188`), `Matrix.mul_adjugate` (`:264`) `M * adjugate M = M.det • 1`, `Matrix.adjugate_mul` (`:269`). Cayley-Hamilton 経路 `Matrix.aeval_self_charpoly` (`Matrix/Charpoly/Basic.lean:211`) |
| **10.28 Alperin-Kuo** | `MonoidHom.transferCenterPow` (`Transfer.lean:229`), `transferCenterPow_apply` (`:235`) `↑(transferCenterPow G g) = g^(center G).index`. 10.18 完成後 5-10 行 |

## 下流被引用 (Isaacs Ch.10+ = なし, BG, Peterfalvi)

### Isaacs 内 (Ch.10 が最終章)

```
Ch.10 の結果が引用される後続 chapter: なし (Index と Bibliography のみ).
```

Ch.10 は **Isaacs FGT の最終 main chapter**. Ch.10 結果を内部利用するのは Ch.10 自身のみで, 真の意味で "葉" の章. ROADMAP 上 ROADMAP.md の Ch.10 項目はこの理由で第 5 波末尾に置かれている.

### BG での引用 (`references/bg/local-analysis.mmd`)

Ch.10 概念に直接対応する BG 引用は **0 件**:

| 検索 | BG hits | 評価 |
|---|---|---|
| `Yoshida` | 0 | Yoshida 10.1 を引かない |
| `Mackey` | 0 | Mackey transfer 10.10 を引かない |
| `principal ideal` | 0 | 10.18 Furtwängler を引かない |
| `Furtwangler` | 0 | 同上 |
| `transitivity of transfer` | 0 | 10.8 を引かない |
| `augmentation ideal` | 0 | §10C 用語を引かない |

BG §4 (L1377-1640) には "metacyclic p-group" の議論があるが, **Isaacs 10.12 とは別の定理** (上記 TL;DR 参照):

| BG | 内容 | Isaacs 対応 |
|---|---|---|
| Lemma 4.10 (L1546) | p odd, R metacyclic noncyclic ⇒ Ω_1(R) elementary abelian of order p^2 | Isaacs 直接対応 **なし** (Ch.10 §10B には Ω_1 構造分析無し) |
| Prop 4.11 (Huppert) (L1554) | p > 3, \|Ω_1(R)\| ≤ p^2 ⇒ R metacyclic (Huppert *EG I* III.11.6) | Isaacs Ch.10 とは **逆方向**. Isaacs 10.12 は metacyclic ⇒ p ∣ \|G:G'\| (transfer 結果), BG 4.11 は Ω_1 ⇒ metacyclic (構造判定) |
| Thm 4.12 (Huppert) (L1588) | p odd, R metacyclic, A p'-operator ⇒ R abelian | Isaacs Ch.10 範疇外. Ch.6 coprime action 系統 |
| Thm 4.16 (Blackburn) | r(R) ≤ 2, [R,A] = R, \|A\| odd ⇒ p > 3 + 構造 | Isaacs Ch.10 範疇外 |

⇒ BG §4 は Isaacs Ch.10 §10B の "Huppert metacyclic" を **概念的に独立した別の Huppert 定理として再構築**している. 共通項は "metacyclic p-group" の定義 (BG L1377: 同じ定義) のみで, 証明戦略・結論ともに異なる. Phase 2a 進行時に BG §4 を書くとき, Isaacs Ch.10 §10B の Lean 形式化は **援用しない**.

**(2026-05-23 audit 補足)** BG §4 と Isaacs §10B Huppert で **共通の subroutine は 1 つだけ**: 「p odd, R metacyclic noncyclic ⇒ Ω_1(R) elementary abelian of order p²」 (BG Lem 4.10 L1546 / Isaacs 10.15 proof L5636 暗黙). 実装時は `OddOrder/GroupTheory/Metacyclic.lean` に小補題化して両方から import. Hall-Higman 1956 共通 cite なし: BG §4 は Hall (regular p-groups) を `[17]`/`[19]` 経由のみ. Peterfalvi 全 mmd `Hall-Higman` 0 件.

### Peterfalvi での引用 (`references/peterfalvi/*.mmd`)

Ch.10 概念の出現は **0 件**. Peterfalvi 本体 (§1-§16) は character theory ベースで transfer 写像を使わず, transfer ベースの章 (Suzuki 付録 05.X) も Isaacs 5.5 (transfer-evaluation) 1 件だけで Ch.10 結果に依存しない (Ch.5 ノート §5C で確認済).

Peterfalvi 付録 06.0 "A Special Case of a Theorem of Huppert" (pp.135-136) は **doubly transitive permutation groups** の Huppert (Huppert-Blackburn *Finite Groups III* Ch.XII §7) で, Isaacs 10.12 と全く別の系統 (permutation group 理論). Ch.10 §10B の metacyclic Huppert との関連性は無い.

### 結論: FT 経路への直接寄与ゼロ

§1G Chermak-Delgado (Ch.1 ノート参照) ・ Ch.9 全章 (ch09_more_subnormality.md 参照) と同じく, Ch.10 全章を **Phase 1 で実装しない** 選択肢が妥当. ROADMAP 第 5 波末尾の Ch.10 項目は "未着手 — BG §4 / Peterfalvi §10-§16 で要求が出てこなければ skip" と注記すべき.

## 章内依存 (Ch.10 内で 10.X が引用される頻度)

`awk` で Ch.10 本文 (L5310-5914) を切り出し grep:

```
最頻 被引用:
- 7  Theorem 10.18  ← principal ideal theorem (10.20-10.27 経路 + 10.28 で結合)
- 3  Theorem 10.8   ← transitivity of transfer (10.9, 10.11, Yoshida 10.1 証明, 10.28 で利用)
- 3  Theorem 10.4   ← C_p ≀ C_p 認識 (10.5 系, 10.7 経由 Yoshida 10.1 に利用)
- 3  Theorem 10.26  ← Nakayama 風 classical adjoint lemma (10.25 で適用)
- 3  Theorem 10.25  ← \|K:G'\|-倍化 (10.18 / 10.28 への橋渡し)
- 3  Theorem 10.16  ← Maschke 一般化 (10.15, 10.17 で利用)
- 3  Theorem 10.15  ← P ◁ N case (10.12 Huppert の核)
- 3  Theorem 10.1   ← Yoshida (10.12, 10.15 で適用)
- 3  Lemma 10.21    ← Δ(K)Δ(G) 構造 (10.22, 10.23, 10.27 で利用)
- 3  Lemma 10.19    ← Δ(G) Z-basis (10.20, 10.21 で利用)
- 3  Lemma 10.13    ← metacyclic 閉性 (10.14, 10.15 で利用)
- 3  Lemma 10.3     ← 10.4 + 10.14 + Yoshida 10.1 系
- 3  Corollary 10.23 ← \overline{Δ(K)} ≅ K/K' (10.24 で利用)
```

**章内ハブ**:
- §10A 軸: 10.3 → 10.4 → 10.5 → 10.6 → 10.7 → (10.8, 10.9, 10.10, 10.11) → **10.1 Yoshida**
- §10B 軸: 10.1 + 10.13 → 10.14 → **10.12 Huppert**. ＋ 並列で 10.16 → 10.17 → 10.15 → 10.12
- §10C 軸: 10.19 → 10.20 → 10.21 → 10.22 → 10.23 → 10.24 → (10.26 → 10.27) → 10.25 → **10.18**. ＋ 10.18 → **10.28**

### 章間依存 (Ch.10 が Ch.1-9 から引く)

`awk 'NR>=5310 && NR<=5914' mmd | grep -oE "(Theorem|Lemma|Corollary|Proposition) [0-9]+\.[0-9]+"` で:

```
2  Theorem 4.7   ← p-group nilpotence class 定理 (10.3 で 1 回, 10B 序文で 1 回)
1  Theorem 6.11  ← p-group ≤1 subgroup ⇒ cyclic/quaternion (10.15 で利用)
1  Theorem 5.6   ← central transfer = pow (10.28 で利用)
1  Theorem 4.8   ← Thm 4.8(a) p odd ⇒ {x | x^p = 1} は subgroup (10.15 で利用)
1  Lemma 5.5     ← transfer-evaluation (10.9 で利用)
1  Lemma 5.12    ← N_G(P) controls C_G(P) fusion (10A 序文で言及)
1  Lemma 4.6    ← \|Z(P)\| ≥ p (10.3 で利用)
1  Corollary 5.22 ← H controls p-transfer (10A 序文)
```

⇒ Ch.10 は **Ch.5 (Transfer) ＋ Ch.4 (Commutators)** を主に引く. Ch.6 引用は 6.11 (p-group 構造判定) のみ. Ch.7 / Ch.8 / Ch.9 引用は **ゼロ** — 並列章なので妥当.

## 視点 4: 先行章節への依存 (per-target) (2026-05-23 audit 統合)

mmd L5310-5914 grep ベースの per-target dep table (audit §4.3 由来):

| Ch.10 target | Cite | mmd | OddOrder 状態 |
|---|---|---|---|
| §10A intro prose | Lem 5.12, Cor 5.22 | L5318 | ✅ Ch.5 既実装 |
| **10.3** | Lem 4.6 (`|Z(P)| ≥ p`) | L5350 | ✅ Ch.4 hub |
| 10.3 | Thm 4.7 (p-group nilpotence class) | L5350 | ⚠️ Ch.4 skeleton, **未証明** |
| 10.9 | Lem 5.5 (transfer-evaluation) | L5479 | ⚠️ mathlib 直接 `transfer_eq_prod_quotient_orbitRel_zpowers_quot` (`Transfer.lean:161`), wrapper 不在 |
| **10.15** | Thm 4.8(a) (p odd: {x: x^p=1} subgroup) | L5636 | ⚠️ Ch.4 skeleton, **未証明** |
| **10.15** | Thm 6.11 (p-group ≤1 subgroup of order p ⇒ cyclic/quaternion) | L5636 | ❌ Ch.6 未着手 |
| 10.28 | Thm 5.6 (central transfer = pow) | L5893 | ✅ mathlib `MonoidHom.transferCenterPow` (`Transfer.lean:229`) 直接 |
| 10.28 | Thm 10.8 (transitivity, 章内) | L5893 | — internal |
| 10.28 | Thm 10.18 (principal ideal, 章内) | L5893 | — internal |

**Phase 1 gating implication**:

- **§10A 単独 (Yoshida 10.1)**: Ch.4 Thm 4.7 必須. Ch.4 §4A-§4B 完成後着手可.
- **§10B (Huppert 10.12 + 10.15)**: **Ch.6 Thm 6.11 待ち** ⇒ Ch.6 完了が gating.
- **§10C (principal ideal 10.18)**: 内部完結 — Ch.4/5 補強不要で **stand-alone 実装可** (FT 不要だが mathlib upstream 価値 HIGH).
- **10.28 Alperin-Kuo**: 10.18 完成 + mathlib `transferCenterPow` で **5-10 行**, Ch.4/5/6 追加実装不要.

## Shared module 配置提案 (`OddOrder/GroupTheory/` 4 files + Ch10 thin glue) (2026-05-23 audit 統合)

Ch.4-7 audit (2026-05-22) で確立した shared module パターンを Ch.10 に適用 (audit §5.3 由来):

```
OddOrder/GroupTheory/Metacyclic.lean          -- IsMetacyclic def, 10.13 closure, 10.14
                                              -- + BG §4 共用 Ω_1 補題 (Lem 4.10 / Isaacs 10.15 暗黙)
OddOrder/GroupTheory/AugmentationIdeal.lean   -- ⭐ HIGH upstream value
                                              -- augmentation, Δ(G), 10.19 basis, 10.20 G^{ab} ≅ Δ/Δ²
                                              -- (class field theory + group cohomology 両方需要)
OddOrder/GroupTheory/MaschkeGroupAction.lean  -- group-action Maschke (10.16, 10.17)
OddOrder/GroupTheory/TransferMackey.lean      -- 10.8 transitivity, 10.10 Mackey
OddOrder/Isaacs/Ch10_MoreTransfer.lean        -- Yoshida 10.1 + Huppert 10.12 + principal ideal 10.18
                                              -- (Isaacs 命名 + 上記 4 module の thin glue のみ)
```

### mathlib upstream 価値 ranking (Phase 1 完成後の余剰時間用) (audit §5.4)

| 候補 | upstream 価値 | コスト |
|---|---|---|
| `AugmentationIdeal.lean` (Δ(G), Thm 10.20 `G^{ab} ≅ Δ/Δ²`) | **HIGH** (class field theory + group cohomology 両需要) | 大 |
| Yoshida 10.1 (`Mathlib/GroupTheory/Transfer/Yoshida.lean`) | MEDIUM (単体で強い結果) | 大 |
| Maschke 群作用版 + Mackey transfer | MEDIUM (mathlib RepresentationTheory / DoubleCoset 補強) | 中 |
| `Subgroup.IsMetacyclic` def | LOW (1 行 def) | 極小 |

⇒ **AugmentationIdeal が単体最高価値**. Phase 1 完成後の最初の mathlib PR 候補.

## 着手順 (提案)

**前提**: Phase 1 で Ch.10 全部を書きたい場合の順序. **実際には ROADMAP では skip 推奨** (上記理由).

FT クリティカル度 + mathlib カバレッジ + 章内依存で並べる:

1. **Ch.5 前提確認**: `MonoidHom.transfer`, `transferFunction`, `focalSubgroup` の Isaacs 流ラッパー (Ch.5 ノート §5A-§5D 既出). Ch.10 §10A 序文 (L5314-5330) の "Ch.5 review" 部分はそのまま Lean docstring に書ける.
2. **`IsMetacyclic G` def** (§10B 序文): 1 行. mathlib upstream 視野で `Subgroup.IsMetacyclic` も検討.
3. **§10A 後半 一般 transfer 補題 (10.6, 10.7, 10.8 transitivity)**: 10.8 は単独で重要. mathlib upstream 候補.
4. **§10A wreath product setup (10.3, 10.4, 10.5)**: C_p ≀ C_p の構成と認識. wreath product 一般 def を mathlib に入れるか, ad-hoc に C_p ≀ C_p のみ書くかは判断.
5. **§10A Mackey transfer (10.10)**: mathlib `DoubleCoset` API ＋ pretransfer. 中規模.
6. **§10A 残り (10.9, 10.11, 10.1 Yoshida, 10.2)**: 章のハイライト. 重い証明.
7. **§10B (10.13, 10.14, 10.16, 10.17, 10.15, 10.12 Huppert)**: Yoshida 10.1 完成後の応用. Maschke は mathlib `RepresentationTheory.Maschke` を group 作用版に拡張.
8. **§10C Δ(G) / Z[G] 流 transfer (10.19, 10.20, 10.21, 10.22, 10.23, 10.24)**: augmentation ideal API を新規構築. **mathlib upstream 候補** (`Mathlib/GroupTheory/AugmentationIdeal.lean` のような場所).
9. **§10C 結論 (10.25, 10.26, 10.27, 10.18 principal ideal, 10.28 Alperin-Kuo)**: 章の終盤. 10.18 は class field theory にも応用があり, mathlib upstream すれば数論側からも利用される可能性.

優先度 (FT クリティカル度 ≅ ゼロ なので mathlib upstream 価値で並べ替え):
- **mathlib upstream 価値 HIGH**: 10.1 Yoshida (独立した強い結果) > 10.18 principal ideal (古典 + class field theory) > 10.10 Mackey transfer (mathlib `DoubleCoset` の応用) > 10.16 Maschke (群作用版)
- **mathlib upstream 価値 MEDIUM**: 10.12 Huppert (有名な結果) > 10.20 G^{ab} ≅ Δ/Δ^2 (cohomology との接続) > 10.28 Alperin-Kuo
- **完備化のための実装**: 10.3-10.9, 10.13-10.17, 10.19-10.27 (中間補題群)

## 開発時の注意点

### mathlib API 確認事項

- **pretransfer vs transfer**: mathlib `MonoidHom.transfer` は abelian target 専用の準同型 (`G →* A`). Isaacs の "pretransfer `V: G → H`" (非可換 target 許容, mod H' で一意) は mathlib `transferFunction` (`Transfer.lean:89`) で表現可能. `transferFunction` は `G ⧸ H → G` だが Isaacs の linear order 入りの transversal による積形と等価.
- **DoubleCoset の方向**: mathlib `DoubleCoset.doubleCoset a H K = H・a・K`. Isaacs は `HgK` 形 (左右同じ). 単に notation の差.
- **wreath product**: **(2026-05-23 audit 訂正)** mathlib v4.29.1 に `Mathlib/GroupTheory/RegularWreathProduct.lean` (Francisco Silva, 2025, 260 行) が既収載. `RegularWreathProduct D Q` 構造体 (中置記法 `D ≀ᵣ Q`), `mul`/`inv`/`Group` instance, `rightHom`/`inl`, `Nat.card (D ≀ᵣ Q) = (Nat.card D)^(Nat.card Q) * Nat.card Q`, `toPerm` (action on `Λ × Q`), `IteratedWreathProduct G n`, **`Sylow.mulEquivIteratedWreathProduct` (`:242`)** (= Sylow `p`-subgroup of `Sym(p^n)` is iso to iterated wreath product — まさに Isaacs 10.4 が要求する装置) まで揃う. `Cp ≀ Cp = (ZMod p) ≀ᵣ (ZMod p)` 直接. **手作り不要**. Suzuki/Sz(q) 用途 (Peterfalvi §05.6 PSU(3,q)) でも同じ恩恵.
- **`MonoidAlgebra ℤ G` = Z[G]**: mathlib 既収載. `MonoidAlgebra.augmentation : MonoidAlgebra ℤ G →ₐ[ℤ] ℤ` のような map が **未収載** — 自前で `def augmentation : MonoidAlgebra ℤ G →+* ℤ := MonoidAlgebra.lift ℤ G ℤ (fun _ => (1 : ℤ))` で 1 行 def できる. `Δ(G) = (augmentation G).ker` で ideal.
- **Maschke 群作用版 (Thm 10.16)**: mathlib `RepresentationTheory.Maschke` はベクトル空間版. 10.16 の "u ↦ u^m が U 上 bijective" は coprime 仮定の同値表現で, 元の Maschke 証明はそのまま group automorphism 作用に通る. mathlib にコピー版を `Mathlib/GroupTheory/Maschke.lean` で新規追加する手も.

### 章内技術的なポイント

- **Lemma 10.6(b)**: x ∉ M ⇒ V(x) ≡ x^p mod M'. `U = {x^i | 0 ≤ i < p}` を transversal に取る Isaacs 流計算は, mathlib `transferFunction` の任意性で書き換え可能.
- **Thm 10.4 の `S_{p^2}` ↪ 引数**: P が `Sym (Fin (p^2))` の部分群と同型, Sylow 一意性で `P ≅ Cp ≀ Cp`. mathlib `Equiv.Perm` ＋ `Sylow.Conj` で可能だが index 計算が技術的.
- **Thm 10.20 (G/G' ≅ Δ/Δ^2)**: 群コホモロジー `H_1(G, Z) ≅ G^{ab}` に直結. mathlib `RepresentationTheory.Homological.GroupCohomology` 周辺で同等内容があるか要調査 (上記 mathlib search では Hochschild-Serre が hit するが H_1 形式は未確認).
- **Thm 10.26 (classical adjoint)**: `Matrix.adjugate` ＋ Cayley-Hamilton で `T(M-S) = (det(M-S))·I`. mathlib `Matrix.mul_adjugate` で直接表せる.
- **Δ(K)Δ(G) と t-成分の Z-module 分解 (10.21)**: Z[G] = ⊕_t Z[K]·t (右剰余類分解の Z-加群版) を補題化する必要. mathlib `MonoidAlgebra` の `Submodule` API で書ける可能性.

### 数論的応用への目配り

**Thm 10.18 (principal ideal theorem)** は class field theory の中核結果のひとつ ("どの ideal class も Hilbert 類体で principal になる" の群論的言明). mathlib 数論セクション (`Mathlib/NumberTheory/ClassNumber/` 等) には未統合. もし Ch.10 §10C を Lean 化するなら, mathlib `RingTheory.Ideal` ＋ `NumberTheory.ClassField` (将来) との橋渡しコメントを section docstring に置くと upstream 時の価値が高まる.

なお Isaacs 自身 (L5666 前後) が "群論的応用は少ない. 主な応用は class field theory" と明記しており, FT 経路では完全に "葉" になる.

## 第 5 波 (Ch.7 / Ch.10) の並列性

ROADMAP は Ch.6 → (Ch.7 と Ch.10 並列) を提案するが, 実状は:

| 章 | FT クリティカル度 | mathlib 新規実装 % | 推奨 Phase 1 状態 |
|---|---|---|---|
| Ch.7 (Thompson J(P), ZJ) | **HIGH** (BG §10 / Peterfalvi §13-§14 で頻用) | 高 (Thompson normal p-complement, J(P), ZJ subgroup は全部新規) | **必須実装** |
| Ch.10 (More Transfer) | **LOW** (BG / Peterfalvi 直接被引用ゼロ) | 高 (Yoshida / Mackey / principal ideal / Δ-ideal が全部新規) | **skip 推奨** |

⇒ 第 5 波の実体は **Ch.7 一本**. ROADMAP 第 5 波の Ch.10 は §1G Chermak-Delgado, Ch.9 と同じく Phase 1 から落として "FT 経路では未着手" 注記する.

## 未解決の疑問

- **Yoshida 10.1 を mathlib upstream する価値**: Ch.10 を skip しても 10.1 単体を mathlib `GroupTheory/Transfer/Yoshida.lean` として書くと汎用性が高い. Phase 1 完成後に余力があれば検討. ただし wreath product の mathlib 整備が前提.
- **augmentation ideal API の mathlib upstream**: 10.18-10.27 を書くなら `Mathlib/GroupTheory/AugmentationIdeal.lean` を作るのが筋. 数論 (class field theory) と表現論 (group cohomology) の両方で需要があるはず. mathlib upstream PR の良い題材だが Phase 1 のスコープを超える.
- **BG §4 Huppert (4.11, 4.12) と Isaacs 10.12 の関係**: 既述の通り **異なる定理**. BG §4 を書くとき Isaacs Ch.10 §10B からは何も借りない. BG §4 の方は Ch.4 Commutators (BG L1377-1440 が Hall regular p-groups 系) + Ch.5 Transfer 系統で十分書ける.
- **Peterfalvi 06.0 Huppert と Isaacs 10.12 の関係**: 全く別物. 06.0 は doubly transitive permutation groups (Huppert-Blackburn). Ch.8 §8A 概念 + Peterfalvi 流ステートメントで書く.
- **`IsMetacyclic G` の mathlib upstream**: 1 行 def なので簡単. mathlib に `Mathlib/GroupTheory/SpecificGroups/Metacyclic.lean` を追加する PR を出してもよい. Ch.10 を skip しても BG §4 / Peterfalvi 別箇所で metacyclic を使うので mathlib 側に integrate しておく価値はある.

## 統計サマリ

| 項目 | 数 |
|---|---|
| 全numbered結果 (Thm/Lem/Cor) | 28 |
| §10A: Yoshida + wreath setup | 11 |
| §10B: Huppert metacyclic | 6 |
| §10C: Furtwängler + Δ-ideal | 11 |
| mathlib 直接対応 | ~3 (11%) |
| mathlib 新規実装が必要 | ~20 (71%) |
| BG / Peterfalvi 直接被引用 | **0** |
| Isaacs Ch.10+ 被引用 | 0 (最終章) |

**FT クリティカル度: LOW** (BG/Peterfalvi 双方で直接被引用ゼロ). Phase 1 では実装せず, ROADMAP 第 5 波で Ch.7 のみ進めて Ch.10 は "未着手 — BG/Peterfalvi 進行中に必要が判明したら戻る" と注記する運用が合理的. §1G Chermak-Delgado, Ch.9 と同列扱い.

## 関連ノート (2026-05-23 audit 統合)

- [`../meta/chapter_investigation_framework.md`](../meta/chapter_investigation_framework.md) — 4 視点 framework テンプレート
- [`../meta/ch08_10_audit_2026_05_23.md`](../meta/ch08_10_audit_2026_05_23.md) — 本ノートに統合した audit synthesis doc (Ch.8/9/10 横断)
- [`ch04_commutators.md`](ch04_commutators.md) — Lem 4.6 (10.3 で使用) / Thm 4.7-4.8 (10.3, 10.15 で使用, **skeleton**) dep
- [`ch05_transfer.md`](ch05_transfer.md) — Lem 5.5 (10.9) / Thm 5.6 (10.28) / Lem 5.12 + Cor 5.22 (§10A intro) dep
- [`ch06_frobenius_actions.md`](ch06_frobenius_actions.md) — Thm 6.11 (10.15 で使用, §10B **gating dep**)
- [`../meta/mathlib_coverage.md`](../meta/mathlib_coverage.md) — 全体 coverage 表 (`RegularWreathProduct` 既存を追記推奨)
- [`../meta/phase2_cross_refs.md`](../meta/phase2_cross_refs.md) — BG §4 vs Isaacs §10B Huppert 別物分類の cross-ref
