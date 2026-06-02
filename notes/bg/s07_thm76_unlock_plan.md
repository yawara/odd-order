# BG Thm 7.6 (Thompson Transitivity) 解禁プラン — 実装中の living note

> 2026-06-03 深夜セッション。目標 = §8–§16 最頻出の **Thm 7.6 (Thompson Transitivity)** を
> 解禁する。critical path 上 (memory `ft-master-roadmap`: 本物の FT 経路 = Track B = BG §7–16)。
> 起点 = `notes/bg/handoff_2026_06_03_s7.md`。live 状況はこの note を随時更新。

## 依存チェーン (検証済み, 2026-06-03)

```
[brick 1] Lem 1.14 centralizer-form  ──┐
[Prop 1.10 ✅][Prop 1.3 ✅]            ├─→ [brick 2] Prop 1.15(b)  ──┐
                                        │   (Goldschmidt)            │
[G 2.6.4 ✅][Thm 6.1=thmA4b ✅]                                      ├─→ [brick 3] Prop 7.5 case(2)
[Prop 1.16 ✅][Prop 1.10 ✅]                                         │   = hypothesis71_of_scn2_or_pLengthOne
                                                                     │
[Thm 7.2 ✅ transitive_of_three_le_rank_center]  ───────────────────┴─→ [brick 4] Thm 7.6 thompsonTransitivity
```

### 検証済みインベントリ (file:line)
- **G 2.6.4** = `Isaacs.Ch01.IsPGroup.normal_inf_center_nontrivial` (`Ch01_Sylow/Main.lean:355`): `IsPGroup p P`,`[N.Normal]`,`Nontrivial N` ⟹ `Nontrivial (N ⊓ center P)`. (= 旧「要 Gorenstein」は誤り; `phase2_cross_refs.md` §5b)
- **Prop 1.10** = `S01.coprime_nilpotent_acts_trivially_of_centralizer_self` (S01:1775): `φ:A→*MulAut G`,`[IsNilpotent G]`,coprime,`C_G(fixedPoints φ)≤fixedPoints φ` ⟹ A trivial. **φ-form** (実装時 M-on-T を φ へ翻訳要)。
- **Prop 1.3** = `S01.centralizer_fitting_le_fitting` (S01:187): `C_G(F(G)) ≤ F(G)` (solvable)。
- **Lem 1.14 normalizer-form** = `S01.normalizer_sup_eq_normalizer_sup_of_pGroup_coprime` (S01:2078)。**centralizer-form は未** → brick 1。
- **Thm 6.1** = `BG.AppA.thmA4b` (`AppA_PStability.lean:1915`): `p≠2`,`IsSolvable G`,`Odd(card G)`,`P∈Syl_p`,`A≤P` 正規 abelian ⟹ `A ≤ oPiPrimePiCore {p} G` (=O_{p',p})。**proper subgroup of min-simple-odd の solvable/odd 供給要** (IsMinimalSimpleOdd から)。
- **Prop 1.16** = `Isaacs.Ch06.nontrivialActionFixedByClosure_eq_top_of_not_isCyclic` (第1式) + `BG.Ch1.S01b.cocyclicFixedByClosure_*` (第2式) + §7 共役ブリッジ `S07.exists_mem_inf_centralizer_ne_bot_of_not_isCyclic` 他。
- **Thm 7.2** = `S07.transitive_of_three_le_rank_center` (S07:865): `Hypothesis71 A`,`q∈(primesOf A)ᶜ`,`3≤rank(center ↥A)` ⟹ `ConjTransitiveOn (kSubgroup A) (hInvariantStar ⊤ A {q})`。
- core spell: `O_{p'}` = `oPiCore {q|q≠p}` (Ch03:1279); `O_p`=`opCore` (Ch01:533); `O_{p',p}`=`oPiPrimePiCore` (Ch03:2812); `F`=`Ch01.fitting` (Ch01:681)。

## brick 1: Lem 1.14 centralizer-form (S01, ~50-80 LOC)

**狙い**: `M` normal p'-subgroup, `T` p-subgroup, `C=C_G(T)`,`N=N_G(T)` ⟹ `C_{G/M}(TM/M) = CM/M`
(sup 形で: 商の centralizer の引き戻し = `C ⊔ M`)。既存 normalizer-form と同じ sup スタイルで述べる。
**証明**: `CM ⊆ C* ⊆ N* = NM` (normalizer-form) ∧ `T⊓M=⊥` ⟹ `C*⊓N = C` ⟹ `C* = (C*⊓N)M = CM`
(Dedekind: `M ≤ C*` は自明 = M↦1; `C*⊓N=C` は x∈N が T 正規化 + TM/M 中心化 + T⊓M=1 ⟹ x が T 中心化)。

## brick 2: Prop 1.15(b) `O_{p'}(C_G(R)) ≤ O_{p'}(G)` (S01, near Prop 1.15(a) @2213)

`G` solvable finite, `R` p-subgroup. **reduction** `O_{p'}(G)=1` 化 (M₀=O_{p'}(G) で商, brick 1 で
`C_G(R)` が `C_Ḡ(R̄)` に全射 ⟹ O_{p'}(C_G(R)) の像 = `C_Ḡ(R̄)` の正規 p'-subgroup ⊆ O_{p'}(C_Ḡ(R̄))=1)。
`O_{p'}=1` case: `M=O_{p'}(C_G(R))`,`T=O_p(G)=F(G)`; `RM=R×M`; `[C_{RT}(R),M]⊆RT⊓M=1`; Prop 1.10
(M on RT, fixedPoints=C_{RT}(M), C_{RT}(C)⊆C_{RT}(R)⊆C) ⟹ M centralizes T; Prop 1.3 `C_G(T)⊆T` ⟹ `M=M⊓T=1`。

## brick 3: Prop 7.5 case(2) (S07:1065, 本体)
mmd L2266-2310。B 構成 (Z(P) cyclic/not 2 分岐, cyclic 側で G 2.6.4) → `Y⊆O_{p'}(X)` を inner claim と
して 3 適用 (special b∈B^#∩Z → special 一般 b∈B^# → Prop 1.16 で一般 X)。bar = mod O_{p'}(X)。
case(1) (p-length one, Thm 6.7 待ち) は **明示 sorry で残す** (今回スコープ外)。
**risk**: bar-quotient 機構 + `Ω₁` + `B=⟨b⟩×Z`。`thmA4b`/`S04e`/`S04g` の商引き戻しパターン流用。

## brick 4: Thm 7.6 (S07:1081, 短い assembly)
`A∈scn3Global p` ⟹ (i) A abelian ⟹ `center ↥A=⊤`,`3≤rank(center ↥A)` from `IsSCN₃` pRank≥3;
(ii) A p-group ⟹ `primesOf A={p}` ⟹ `kSubgroup A = opiCoreInG {p}ᶜ (C_G(A))` 橋; `q≠p`⟹`q∈{p}ᶜ`;
(iii) `A∈SCN₂` (SCN₃→SCN₂) で Prop 7.5(2) ⟹ `Hypothesis71 A`; Thm 7.2 適用。

## 実装順 / コミット境界
1. brick 1 (Lem 1.14 cent-form) — S01, 単独 build-green commit。
2. brick 2 (Prop 1.15(b)) — S01, brick1 を使用、単独 commit。
3. brick 4 を先に試す? いや brick 3 が前提。brick 3 (Prop 7.5(2)) — S07, 最重。
4. brick 4 (Thm 7.6) — S07, brick3 直後に同 commit か別 commit。
各 brick: axiom-clean 確認 (`#print axioms` / AxiomsCheck 登録) + anti-scaffold (仮説 hoist 禁止)。
