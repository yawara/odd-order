# BG §4 Thm 4.16 (Blackburn rank≤2 分類) 着手 引き継ぎ書 — 2026-05-30

> 次セッションが **cold start で D = Thm 4.16 に着手**するための self-contained 手順。
> 全体計画 = [`notes/bg/s04_implementation_plan_2026_05_30.md`](s04_implementation_plan_2026_05_30.md) (§4 全 20 結果の DAG + ルート決定 + 工数)。本書はその **Thm 4.16 焦点版 + v1 完了後の現状スナップショット**。
> issue = `issues/0051-bg-s04-thm-4-16-blackburn.md`。

## 0. タスク

BG **Theorem 4.16 (Blackburn)** を sorry-free / axiom-clean で形式化する。

**statement** (`references/bg/local-analysis.mmd` L1636, PDF printed p.40):
> p 奇素数, R 非自明 p-群, A を R の p′-自己同型群, `r(R)≤2`, `[R,A]=R`, `|A|` odd ⇒ **p>3** かつ R は
> (1) abelian, **or**
> (2) `R = R₁∘R₂` (central product): R₁ は **exponent p の extraspecial 群** (位数 p³), R₂ は **cyclic** で `Ω₁(R₂)=R₁'`。

形式化先: `OddOrder/BG/Ch1_Preliminary/S04_PGroupsSmallRank.lean` (既存) + 新規 `OddOrder/GroupTheory/CentralProduct.lean`。

## 1. ⚠ 進め方 (scaffold trap — 最重要)

Thm 4.16 は §4 最難。memory `scaffold-sorry-free-not-done` が最も効く箇所:
- **`/goal` 単発で回さない** (memory `goal-command-spec`: design/multi-sub 型に不適)。
- **設計先行 + sub-issue 分割必須** (§6 のロードマップ参照)。
- hard content (Prop 4.11 Huppert 等) を**未充足仮説に hoist して "sorry-free" に見せない**。判定は hypothesis constructibility。
- 0016/§4 v1 と同型に「逐次 build-green workflow + adversarial verify + 自律 fix」で回すが、**Thm 4.16 本体 stage は設計を詰めてから**。

## 2. v1 で揃った前提 (2026-05-30 完成、そのまま使える)

| 前提 | decl | ファイル |
|---|---|---|
| PRank 性質 | `pRank_le_iff` / `le_pRank` / `rank` (全素数) / `pRank_mono_of_le` / `IsElementaryAbelian.card_eq_pow_finrank` / `log_card_eq_finrank` (2形の橋) | `OddOrder/GroupTheory/PRank.lean` |
| SCN₃ | `IsSCN₃` / `IsSCN_n` / `isSCN_iff_isMaximalAbelianNormal` (Prop 4.4(a)) / `IsSCN_n.le_pRank` | `OddOrder/GroupTheory/SCN.lean` |
| Lem 4.7 ⇒ | `scn3_empty_of_pRank_le_two` (r≤2 ⇒ SCN₃=∅) | `S04_PGroupsSmallRank.lean` |
| Lem 4.2 | `commutatorElement_pow_left/right_of_central` / `mul_pow_eq_mul_commutator_pow_of_central` | `S04_PGroupsSmallRank.lean` |
| Lem 4.5(a) 部分 | `exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic` (存在) / `exists_normal_isElementaryAbelian_card_prime_sq_of_prime_sq_dvd_card_omega1Center` (normal abelian-center case) | `S04_PGroupsSmallRank.lean` |
| **GL(2,p) 分岐エンジン** | `isPGroup_commutator_of_faithful_two_dim_charP` (= Thm 2.6(b) 導来形。Thm 4.16 の Case B-2 と Cor 4.19 で使う) | `S04_PGroupsSmallRank.lean` |
| 0016 critical | `IsCritical` / `isCritical_exists` / `autCentralizer` / `Omega.exponent_eq_of_class_le_two` / `mul_pow_eq_commutator_pow_mul_of_class_le_two` / `centralizer_eq_self_of_maximal_abelian_normal` | `OddOrder/GroupTheory/CriticalSubgroup.lean` |
| Thm 2.6 | `odd_two_dim_sylow_abelian` (GL(2,p) 分岐の出典) | `S02_Representations.lean` |
| **issue 1 API (2026-05-30 完了)** | `IsCentralProduct` / `of_le_centralizer` (Case B-1 producer) / `inf_le_centralizer` (R₁⊓R₂≤Z(R) 導出) ・ `IsExpPExtraspecial` / `pow_eq_one` ・ `Agemo` (𝒰ⁿ) / `anti` / `characteristic` | `CentralProduct.lean` (新規) / `IsExtraspecial.lean` / `OmegaSubgroup.lean` |
| **I-1b Prop 1.6(b) R-内部形 (2026-05-30 完了)** | `actionCommutator_restrict_self_eq_top` (`[[R,A],A]=[R,A]` ⇒ `[N,A]=N`, Thm 4.12(a) a-1「R=[R,A] WLOG」) + `..._map_subtype_eq` (G 内等式) + `..._toMulAutHom_map_subtype_map_inl` (一般橋) | `OperatorQuotientAction.lean` (新規) |
| **N-4 φ̄ lift = Ch04 既存** | `IsAInvariant.quotientMulAutHom` (商作用持ち上げ) + `actionCommutator_quotient_eq_map` (descent) ⚠ 実名二重 nest (`_root_` 欠落, Ch04 修正待ち) | `Isaacs/Ch04_Commutators/Main.lean:2248` |

## 3. Thm 4.16 に至る未実装の前提 (Wave 2 — D の実質的大半)

Thm 4.16 本体の前に要る (sorry なしで deferred 中):
- **Prop 4.3(a) cl≤3/p>3 分岐** (cl≤2 は `Omega.exponent_eq_of_class_le_two` で済): regular p-group collection, `(uv)^n` triple-commutator。mmd L1410-1472。
- **Lem 4.5 general** (noncyclic + **cyclic** Ω₁(Z(R)) = extraspecial case): Gorenstein 5.4.10 substance。"noncyclic R ⇒ Ω₁(Z(R)) noncyclic" は**偽**なので v1 の abelian-center 版では覆えない。+ Lem 4.5(b) (cyclic index p ⇒ Ω₁≅E_{p²}, G 5.4.3/4.4), 4.5(c)。
- **Prop 4.8** (r≤2 ⇒ exp p で |R|≤p³, p>3 ⇒ Ω₁ exp p): 4.5+4.3+|R|帰納。
- **Prop 4.11 (Huppert)** (p>3, |Ω₁|≤p² ⇒ R metacyclic): BG 自前再証明 (Huppert Satz III.11.6), mmd L1556-1586。**§4 第2の山**。`IsMetacyclic` def 済。
- **Thm 4.12 (Huppert)** (metacyclic + p′-op A, [R,A]=R ⇒ R abelian 他): mmd L1590-1622。
- **Lem 4.13/4.14** (SCN₃=∅, q∤p, q∣|Aut R| ⇒ q∣p²-1, q<p): Gorenstein 5.4.15 + Aut↔GL(2,p) 橋。
- **Lem 4.15** (S extraspecial ≤ R, [S,R]⊆S' ⇒ R=S·C_R(S)): Gorenstein 5.4.6。`IsExtraspecial` 活用。

## 4. 新規 API (repo/mathlib 不在、要作成)

- **`CentralProduct.lean`** (新規): `IsCentralProduct R R₁ R₂ : Prop := R = R₁⊔R₂ ∧ ⁅R₁,R₂⁆=⊥ ∧ R₁⊓R₂ ≤ Subgroup.center R`。Thm 4.16(2) 専用、最小述語。
- **exp-p extraspecial**: `IsExtraspecial p G ∧ Monoid.exponent G = p` (= M(p,1))。`IsExtraspecial.lean` 拡張 or S04 局所。
- **agemo `℧ⁿ(R)=⟨x^{pⁿ}⟩`** (`OmegaSubgroup.lean` に追加): Prop 4.11/Thm 4.12 で使用。`Omega` の双対。
- **Aut(E_p^n)≅GL(n,p) 橋** (Lem 4.13/Thm 4.16 Case B-2): mathlib `Matrix.card_GL_field` 周辺を確認、無ければ自前。

## 5. Thm 4.16 証明構造 (BG mmd L1638-1704)

`|R|` 帰納, `|Ω₁(R)|` で場合分け:
- **準備**: r(R)≤2 ⇒ SCN₃=∅ (Lem 4.7⇒ ✅ `scn3_empty_of_pRank_le_two`), Lem 4.13 で p>3。
- **Case A: |Ω₁(R)|≤p²** ⇒ Prop 4.11 で R metacyclic, Thm 4.12 + [R,A]=R で R abelian → **条件(1)**。
- **Case B: |Ω₁(R)|>p²** ⇒ Prop 4.8 で S=Ω₁(R) 指数 p 位数 p³ extraspecial, C=C_R(S) cyclic (Lem 4.5)。
  - **B-1**: R が S/S′ 中心化 ⇒ Lem 4.15 で R=S·C → **条件(2)** (R₁=S, R₂=C)。
  - **B-2**: R が S/S′ 非中心化 ⇒ T=[R,S] 位数 p², **GL(2,p) 合同 `j²≡1 mod p` と `j²≢1` の矛盾** (`isPGroup_commutator_of_faithful_two_dim_charP` エンジン) → このケースは起きない。

## 6. 推奨着手順 (sub-issue, design §6 準拠)

1. **新規 API 束** (build-green 向き): `CentralProduct.lean` + exp-p extraspecial + agemo `℧`。
2. **Prop 4.3(a) cl≤3 + Lem 4.5 general/4.5(b)(c)** (Gorenstein 5.4.10/5.4.3 行間読み)。
3. **Prop 4.8 + Prop 4.11 Huppert + Thm 4.12** (§4 第2の山, 帰納密)。**設計先行**。
4. **Lem 4.13/4.14/4.15** (aut order + extraspecial commutator)。
5. **Thm 4.16 本体** (Case A/B 組む + GL(2,p) 合同)。**設計先行, 複数 sub-stage** (Case A / Case B-1 / Case B-2 を別々に)。

各 sub-issue は 0016/§4 v1 と同型の「逐次 build-green workflow + adversarial verify + 自律 fix」で回せる。issue 1, 4 は build-green 単発向き、issue 3, 5 は設計先行 (multi-sub)。

## 7. 参照パス (絶対)

- BG §4 原典: `/home/ywr/odd-order/references/bg/local-analysis.mmd` L1359-1788 (Thm 4.16 本体 L1636-1704, Lem 4.5 L1481, Prop 4.11 L1554, Thm 4.12 L1588, Lem 4.15 L1632)
- Gorenstein 行間: `/home/ywr/odd-order/references/gorenstein/finite-groups.mmd` L4181-4231 (5.4.15 = Lem 4.7⇐/4.13), 5.4.10 (Lem 4.5 general), 5.4.6 (Lem 4.15)
- 全体計画: `/home/ywr/odd-order/notes/bg/s04_implementation_plan_2026_05_30.md`
- 既存 S04: `/home/ywr/odd-order/OddOrder/BG/Ch1_Preliminary/S04_PGroupsSmallRank.lean`
- エンジン: `CriticalSubgroup.lean` / `S02_Representations.lean` (Thm 2.6) / `PRank.lean` / `SCN.lean` / `IsMetacyclic.lean` / `IsExtraspecial.lean`
- 新規作成先: `/home/ywr/odd-order/OddOrder/GroupTheory/CentralProduct.lean`

## 8. 次セッションの最初の一歩

> **更新 (2026-05-30)**: ~~issue 1 (新規 API 束)~~ ✅ + ~~I-1b (Prop 1.6(b) R-内部形)~~ ✅ **完了**。
> - issue 1: `IsCentralProduct` / `IsExpPExtraspecial` / `Agemo` (commits 4656738/560312b/4d0269a)。
> - I-1b: `actionCommutator_restrict_self_eq_top` @ `OperatorQuotientAction.lean` (commit 3641c6a)。
> - **N-4 の φ̄ lift 半分は Ch04 既存** (`quotientMulAutHom`@Ch04:2248) と判明 (設計書 §2 N-4 訂正済、再実装不可)。残 N-4 = **Maschke complement bridge のみ** = `notes/bg/s04_n4_maschke_bridge_design.md`。
> - 3 大難所設計 = **`notes/bg/s04_prop411_thm416_design.md`** (scaffold-trap audit + sub-issue I-0a..I-5)。

**次の選択肢** (どちらも gate 解消済): (A) **issue 2 = Prop 4.3(a) cl≤3 + Lem 4.5 general** (Wave 2、Prop 4.11/4.8 の前提)、または (B) **N-4 Maschke bridge** (`s04_n4_maschke_bridge_design.md`、Thm 4.12(a)/4.16 B-2 を開く)。設計書の依存表・risk を必ず先に読む。⚠ **既存 `quotientMulAutHom` の二重 nest 名 (Ch04 `_root_` 欠落) に注意** — Maschke 着手前に Ch04 修正が要る (spawn task 済)。

**最重要 risk (設計書より)**: 最深 scaffold-trap gate = **N-4 (A の R/S 商作用 + Maschke A-invariant complement)** — Thm 4.12(a) と Thm 4.16 Case B-2 が両方依存するが repo 不在。`MulAction A (R/S) := sorry` で誤魔化す誘惑が最大なので**最初に genuine 実装**。Thm 4.16 B-2 の `j²≡1` 矛盾は**純 ZMod p 算術で閉じる** (GL engine 経由でない — mis-routing 注意)。

cold start チェック:
1. `git log --oneline -8` で HEAD 確認。issue 1 完了後の HEAD は commit 9f9db42 (設計書) 付近 (並行 Peterfalvi セッションの commit が混在し得る)。
2. `lake build OddOrder` が green か (Peterfalvi S09 の既知 sorry 以外 RC 0)。
3. 本書 §2 の前提 (issue 1 API 行 含む) が実在するか `grep` で確認 (drift 注意)。
4. **`notes/bg/s04_prop411_thm416_design.md`** + `notes/bg/s04_implementation_plan_2026_05_30.md` を通読してから着手。
