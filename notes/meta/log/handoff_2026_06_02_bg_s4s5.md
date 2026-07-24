# Handoff 2026-06-02: BG §4-§5 セッション (Thm 5.3→5.5→4.17→4.18 完成)

> **✅ 完遂済 (2026-06-02 続行セッション)**: 本 handoff の計画どおり **Thm 5.6 (d09897a) と
> Thm 5.7 (a303385) が完成し、S05 は sorry-free = §5 完結**。本ファイルは歴史的記録。
> 実装の差分・教訓は [`notes/bg/s05_thm55_design_2026_06_02.md`](../bg/s05_thm55_design_2026_06_02.md)
> の ✅✅✅/✅✅✅✅ 節を参照 (5.7 は scaffold 仮定を pRank→rank に修正、Cor 4.19 は
> 固定点論法で直接実装、Prop 1.2 は S01 形式化済みだった)。

> **次セッションの開始点 (当時)**。現在地 + Thm 5.6/5.7 の実装計画 + 今セッションで学んだ
> Lean 罠。設計詳細の正本 = [`notes/bg/s05_thm55_design_2026_06_02.md`](../bg/s05_thm55_design_2026_06_02.md)。

## 現在地 (main = a403b93, build green 3551+ jobs, AxiomsCheck 全 pass)

今セッションで **sorry-free・axiom-clean・AxiomsCheck 登録済**になった BG 結果:

| 結果 | Lean 名 | commit |
|---|---|---|
| Thm 5.3 + 5.3(d) + Cor 5.4 | `S05.narrow_iff_exists_maximalElementaryAbelian_card_prime_sq` / `narrow_centralizer_decomp` / `narrow_iff_exists_card_prime_centralizer_pRank_le_two` | 03fa5f9 (merge d6af523) |
| Lem 1.9 多段昇格 | `S01.coprime_stabilizes_chain_trivial` (AppA private→public) | 20dcd6f |
| Lem 4.17 | `S04.isPGroup_commutator_of_mulAut_odd_of_pRank_le_two` (S04 §4G) | eef1bcb |
| Thm 5.5 | `S05.solvableAut_of_narrow` | d5545b3 / 7b87424 / 90fac6f |
| **Thm 4.18** | `S04.solvable_structure_of_pRank_le_two` (**新 leaf `S04g_Thm418.lean`** §4H) | bc3f2f1 |

**S05 の残 sorry = 2 つだけ**: `narrow_sylow_solvable_structure` (Thm 5.6, S05 末尾) と
`derived_le_fitting_of_centralizer_pRank_le_two` (Thm 5.7)。**ゲートは全部開いている**。

main は origin から 50+ commits ahead (push は指示時のみ)。worktree: B5 等 6 本残置
(B5 は全 merge 済 clean / P4 に未コミット WIP / R1 はコミット済未 merge 3 commits —
別セッションの成果、詳細は memory round-2 節)。

## 次: Thm 5.6 (`narrow_sylow_solvable_structure`) の実装計画

mmd L1945-1953。statement は scaffold 済 (S05 末尾、結論 5 連は **Thm 4.18 と同語彙**)。
`by_cases hrank : pRank ↥S p ≤ 2` で分岐:

### r(S) ≤ 2 分岐 (4.18 直結)

残る唯一のピース = **Sylow rank 橋** (~50行):
`pRank G p ≤ pRank ↥S p` (S : Sylow p G)。証明: 任意の elem-ab `p`-部分群 E は
`IsPGroup.exists_le_sylow` + Sylow 共役で `S^g` 内に入る → `E ≃ E-in-S^g` ≤ S^g ≅ S
(共役 iso `MulAut.conj` で pRank 不変) → `log card E ≤ pRank ↥S p`。
これで `pRank G p ≤ 2` → `S04.solvable_structure_of_pRank_le_two hodd hp_mem hrank`
がそのまま 5 連を返す (語彙一致を確認済み)。

### r(S) ≥ 3 分岐 (hpl が効く)

`hpl h3 : hasPLengthOne p G`。`core418` (S04g private) の **narrow 版ミラー**を作る:

1. `Ḡ := G ⧸ O_{p'}(G)`、`R̄ := O_p(Ḡ)`。**p-length one ⟺ Ḡ/R̄ が p'-群** (def 直結)
   → `R̄` は Ḡ の Sylow `p`。
2. `R̄ ≅ S` (Sylow lift: `pRank_quotient_le_of_coprime` の中の「逆像の Sylow ≅ 商の
   p-部分群」議論と同じ持ち上げ; 共役で S に一致)。**IsNarrow の iso-transport 補題**
   (~20行) が要る: `IsNarrow p R → R ≃* R' → IsNarrow p R'` (witness を equiv で写す)。
3. Hall–Higman で `C̄ := C_Ḡ(R̄) ≤ R̄` (core418 と同一)。
4. **Lem 4.17 の代わりに Thm 5.5** を `A := Ḡ ⧸ ker(conjNormal)` に適用:
   - 5.5(a): `A/O_p(A)` abelian p'-群 → `G'` の引き戻しは「O_p(A) の引き戻しの引き戻し」
     に入る → `G' ≤ O_{p',p}(G)` 系の包含 ((c)(d)(e) は 4.18 の組み立てがそのまま流用可能 —
     g''-range が R̄ でなく O_{p',p}-側に入る点だけ調整)。
   - (a) 最大素因子: Lem 4.13 の代わりに **5.5(b)**: q ≠ p prime ∣ |A| → Cauchy で
     位数 q の元 (p'-元) → orderOf ∣ p−1 → q ≤ p−1 < p。
   - (b): (a) + odd → Ḡ は p-群 → `O_{p'}(G)` complement (4.18 の hb と同一コード)。

core418 の組み立てコードは S04g にあるので、narrow 版は **S04g に並べるか S05 に private
で置く** (5.5 を使うので S05 側が import 的に自然 — S05 は S04g を import に追加する必要あり)。

### Thm 5.7

Prop 1.2 (chief-factor 還元) の repo 状況を**まず確認** (S01; audit memo では「引用 6 箇所」
とあるので形式化済みの可能性が高いが名前未確認)。
構造: chief factor `U/V ⊆ F(G)` ごとに `O_q(G)` narrow → Thm 5.5 で `G'` が中心化 →
Prop 1.2 で `G' ≤ F(G)`。Cor 4.19 (mmd L1754-1762, `(G/C_G(U/V))'` p-群 + faithful
irreducible → `G' ≤ C`) を先に S04g に足すと 5.7 が素直になる。

## 今セッションの Lean 罠 (新規分; 既知分は design note §5)

1. **namespace 入れ子事故 第2弾**: Ch03 の `Subgroup.IsPiGroup` の実名は
   `OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup` (`Ch03.Subgroup.IsPiGroup` で参照、
   `le_oPiCore` も同様)。`quotientMulAutHom` (Ch04 内宣言) と同じパターン。
2. **oPiPrimePiCore の π'-集合**: 内部表現は `{q | q ∉ ({p} : Set ℕ)}`。
   `{r | r ≠ p}` とは集合として等しいが、**`QuotientGroup.mk'` の instance が絡む位置では
   rw できない** (motive ill-typed)。⇒ N をこの内部形で `set` し、`{r|r≠p}` 形が要る場所
   (card / (a)) では **plain oPiCore の下でのみ** set-rw する (`G ⧸ A` の型は Normal 不要
   なので card-rw は安全)。
3. **`orderOf_injective` は要素を明示**: `orderOf_injective f hf x : orderOf (f x) = orderOf x`
   を expected-type 推論で使うと `f ?x ≟ ↑x` の単一化に失敗する。
   `have h : orderOf (N.subtype ⟨x, hx⟩) = orderOf ⟨x, hx⟩ := orderOf_injective ...` と
   f-適用形で書き、defeq (`exact h`) で coe-形へ渡す。
4. **`Nat.eq_prime_pow_of_unique_prime_dvd`** は `n = p ^ n.primeFactorsList.length` の
   **直接等式** (∃ でない)。これを `rw [hk]` すると **指数内の `n` まで書き換わり自己参照**
   になる → `conv_lhs => rw [hk]` で左辺限定。
5. `positivity` は変数 `p` の `p ^ m ≠ 0` を出せない → `(pow_pos hprime.pos m).ne'`。
6. `set`-変数が**型レベル** (例 `ψ : G →* MulAut ↥R` の R) に出ると `rw [hR_def]` は
   motive 死。set は zeta-透過なので **rw せず `exact` の defeq に任せる**のが正解。

## 検証コマンド

```
lake build OddOrder OddOrder.AxiomsCheck   # green 確認
grep -n "sorry" OddOrder/BG/Ch1_Preliminary/S05_NarrowPGroups.lean  # 宣言 2 件のみ
```
