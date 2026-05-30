# BG §4 — N-4 残り半分: Maschke A-invariant complement bridge 設計書

> ✅ **実装完了 (2026-05-30, commit 91fc115)** — `OddOrder/BG/Ch1_Preliminary/OperatorMaschke.lean`,
> `exists_aInvariant_complement_in_omega1_quotient`, sorry-free / axiom-clean。
> ⚠ **本設計書からの逸脱**: §2.5/§2.6 が想定した `Representation.mapSubmodule` + `asModule` +
> `MonoidAlgebra.Submodule.exists_isCompl` 直接適用は, **`asModule` の `AddCommMonoid` 二重 instance**
> (`deriving` 由来 vs `AddCommGroup.toAddCommMonoid`) が defeq だが syntactic 不一致で
> `exists_isCompl` 適用が型不整合 → 詰む (親書 §3.1 が予言した "asModule defeq地獄")。
> **回避**: `Subrepresentation ρ` (= V=`Additive ↥E` 上の不変部分群束, asModule 合成不要) +
> `IsSemisimpleRepresentation ρ` (mathlib Maschke が instance 提供) の
> `ComplementedLattice.exists_isCompl` を使用。instance が V 上で一貫し trap 回避。
> 商作用 `φ̄` は予告どおり既存 `quotientMulAutHom` (Ch04) を使用 (再発明せず)。

> **目的**: BG Thm 4.12(a) step a-3 / Thm 4.16 B-2 が要求する
> 「商 `R⧸S` の `Ω₁` を `F_p[A]`-加群と見て、与えられた A-submodule の **A-invariant
> complement** を **subgroup-of-`R` 形 (`S ≤ X ≤ R`, `X⧸S` が complement, `X` A-invariant)**
> で取り出す」橋の **実装設計**。本書は **DESIGN ONLY** — Lean は書かない。
>
> 親設計書: [`s04_prop411_thm416_design.md`](s04_prop411_thm416_design.md) §2 N-4 / §4.2 a-3 / §5.5 B-2。
> 作成 2026-05-30。全 file:line は精読・確認済 (mathlib v4.30.0-rc2 pin)。

---

## 0. EXECUTIVE SUMMARY — feasibility が親書 ⭐⭐ より大幅に良い理由

親設計書 §2 N-4 は本件を「§4 最深ゲート ⭐⭐」とし、特に
**「`φ̄ : A →* MulAut (R⧸S)` の商持ち上げが repo に無い」**ことを最大リスクとした。
**これは現状では誤りで、持ち上げは既に sorry-free 実装済**:

| N-4 を構成する 4 部品 | 状態 | 場所 |
|---|---|---|
| **(L) 商持ち上げ** `φ̄ : A →* MulAut (R⧸S)` (S A-inv normal) | ✅ **実装済 sorry-free** | `IsAInvariant.quotientMulAutHom` @ `Ch04_Commutators/Main.lean:2248` |
| (L) action 公式 `φ̄(a)[g]=[(φ a)g]` | ✅ 実装済 (`@[simp]`) | `quotientMulAutHom_apply_mk'` @ Ch04:2266, `_apply` @ Ch04:2274 |
| (R) 不変部分群への制限 `A →* MulAut ↥H` | ✅ **実装済 ×2** | `IsAInvariant.restrict` @ `Ch03:3044`, `IsAInvariant.toMulAutHom` @ `Ch04:2198` (重複) |
| **(M) Maschke complement → subgroup** | ❌ **needs-impl (本書の対象)** | — |

つまり本書が設計するのは **(M) のみ**: Ω₁ の `F_p[A]`-加群化 + mathlib Maschke 呼び出し +
**module complement ↔ subgroup-of-`R` 変換**。さらに精読の結果、(M) の各ステップは

- Ω₁ の `ZMod p`-加群化 = repo `IsElementaryAbelian.zmodModule` (PRank.lean:83) **既存**
- A-action の `ZMod p`-線形性 = **自動** (`AddMonoidHom.toZModLinearMap` @ mathlib `Algebra/Module/ZMod.lean:81`: ZMod n-加群上の任意の加法準同型は ZMod n-線形)
- subgroup ↔ submodule 対応 = **自動** (`ZMod.smul_mem` @ ZMod.lean:67: ZMod n-加群の部分群は scalar 閉)
- Maschke 本体 = `MonoidAlgebra.Submodule.exists_isCompl` @ mathlib `RepresentationTheory/Maschke.lean:162`

と全て既存ブロックの**接続**に帰着する。**新規に証明すべき「数学的に重い」核は無い**。
重さは「型の張り合わせ (Additive / asModule / toAddSubgroup / comap mk') の配管」。

**feasibility 判定**: **Tractable (中)**。⭐⭐ ではなく **⭐ 配管中心**。最大の罠は数学的困難ではなく
**親書が警告した未構成 instance 詐欺 (`MulAction A (R⧸S) := sorry`) を、もう存在する
`quotientMulAutHom` を見落として再発明し sorry で埋めること**。**実装者は本書 §0 の表を最初に確認せよ**。

---

## 1. 数学的内容 (BG が要求する正確な主張)

### 1.1 使用文脈 (どこで何の complement を取るか)

**Thm 4.12(a) a-3** (mmd L1602-1608): `R` metacyclic, `S` = `R'` を含む A-invariant cyclic
maximal subgroup, `R⧸S` abelian。`R⧸S` の `Ω₁` の中で **A-submodule `W := Ω₁(R)S/S`**
(= `(Ω₁(R) ⊔ S)/S` の像) の **A-invariant complement `X/S`** を取り、`X` が cyclic で
maximal 性から `X=S` を導き `Ω₁(R/S)=Ω₁(R)S/S` を結論。

**Thm 4.16 B-2** (mmd L1654-1704): `C := C_R(S)` (cyclic), `C_R(T)/C` が elementary abelian、
**`TC/C` の A-invariant complement `X/C`** を取り `X=⟨x⟩` cyclic を得て GL(2,p) 合同矛盾へ。

両者とも形は同一: **「abelian p-section `Q := N⧸S` (S ≤ N, ともに A-invariant normal),
その `Ω₁(Q)` 内の与えられた A-submodule `W` に A-invariant complement を取り、
`R` 内の subgroup として返す」**。複製を避けるため **single API** に一般化する (§4)。

### 1.2 なぜ Maschke が使えるか (coprimality)

`|A|` と `|R|=p^k` は coprime (`hcop : Nat.Coprime (Nat.card A) (Nat.card R)`, 親 signature)。
`Ω₁(Q)` は exponent `p` の elementary abelian ⇒ `F_p = ZMod p` 上のベクトル空間。
Maschke は `|A|` が係数体 `ZMod p` で可逆を要する。`p ∤ |A|` は coprime から:
`p ∣ |R|` かつ `gcd(|A|,|R|)=1` ⇒ `p ∤ |A|` ⇒ `(|A| : ZMod p) ≠ 0` ⇒ `NeZero (Nat.card A : ZMod p)`。
**これが Maschke の `[NeZero (Nat.card G : k)]` instance (Maschke.lean:139) を充足する唯一の鍵**。

> ⚠ **A の有限性が必須**: mathlib Maschke は `[Finite G]` (= ここで A) を要求 (Maschke.lean:139)。
> 親 signature は `[Finite A]` を持つ (s04 §4.1 / §5.1) ので OK。

---

## 2. (M) の構成 — module 層 (Ω₁(Q) を `F_p[A]`-加群にする)

### 2.1 ステップ M-a: Ω₁(Q) を抽象群として確保

`Q := N ⧸ S` は abelian (使用文脈で `R'≤S` or `[N,N]≤S` ⇒ `Q` abelian を別途与える)。
abelian p-群の `Ω₁` は **elementary abelian**。repo には 2 形ある:

- `Omega Q p 1` (closure 形, `OmegaSubgroup.lean:59`) — 一般群で正しい `Ω₁`。
- `omega1OfAbelian Q (⊤ : Subgroup Q) p hQ` (`OmegaSubgroup.lean:190`) — abelian 専用、
  `{g | g ∈ ⊤ ∧ g^p=1}` をそのまま subgroup 化。

abelian `Q` では両者一致 (closure が既に部分群)。**設計判断**: module 化には
**`E := ↥(Omega Q p 1)` を使い、`IsElementaryAbelian p E` を補題で得る** (下記 N-needs)。
理由: 最終結果を `Omega R p 1` (closure 形) で書く親 signature (s04 §5.1) と整合。

> **needs-impl (軽) M-a-1**: `abelian Q ⇒ IsElementaryAbelian p ↥(Omega Q p 1)`。
> 現状 repo に `Omega … IsElementaryAbelian` 補題は無い (grep 0 hits)。
> `Omega.mem` の特徴付け (abelian で `g ∈ Omega ↔ g^p=1`) + commutativity から。
> mmd 依存無し・標準。**これは genuine な小補題で hoist 不可** (本書では実装しないが、
> 実装者は (M) の最初に sorry-free で出すこと)。

### 2.2 ステップ M-b: `Additive E` を `ZMod p`-加群に

`E` elementary abelian ⇒ `h : IsElementaryAbelian p E` ⇒
`letI : Module (ZMod p) (Additive E) := h.zmodModule` (PRank.lean:83, **既存**)。
これは `IsMulCommutative E` (= `E` commutative) と `∀x, x^p=1 ⇒ p•x=0` から
`AddCommGroup.zmodModule` を被せる構成。**[NeZero p] 要** (PRank.lean:83 の制約) —
`[Fact p.Prime]` から `NeZero p` は自動。

### 2.3 ステップ M-c: A-action を `ZMod p`-線形に持ち上げ

**ここが「持ち上げが無い」という親書の懸念が解消する箇所**。

1. **既存の制限作用**: `φ̄ : A →* MulAut Q` (= `quotientMulAutHom hS`, Ch04:2248) を、
   `Ω₁(Q)` が `φ̄`-invariant (∵ `Omega.characteristic` instance @ OmegaSubgroup.lean:89 ⇒
   `IsAInvariant.of_characteristic` @ Ch03:2950) であることを使い、
   `ψ : A →* MulAut E := (hΩinv).restrict` (`IsAInvariant.restrict` @ Ch03:3044, **既存**) に制限。

2. **`MulAut E → AddAut (Additive E)` 関手**: `MulEquiv.toAdditive` (mathlib
   `Algebra/Group/Equiv/TypeTags.lean:42`) で各 `ψ a : E ≃* E` を `Additive E ≃+ Additive E` に。

3. **`AddEquiv → ZMod p-linear 自動線形性**: その `AddEquiv` の `toAddMonoidHom` を
   `AddMonoidHom.toZModLinearMap p` (mathlib `Algebra/Module/ZMod.lean:81`, **既存**) に通すと
   `Additive E →ₗ[ZMod p] Additive E`。
   **核心**: `ZMod.map_smul` (ZMod.lean:62) ＝「ZMod n-加群上では任意の加法準同型が ZMod n-線形」。
   ゆえに **A の `ZMod p`-線形性は自動で出る。手で `map_smul` を証明する必要は無い**。
   さらに可逆性 (linear **equiv**) も `AddEquiv` 由来で自動 ⇒ `Additive E ≃ₗ[ZMod p] Additive E`。

4. **`Representation (ZMod p) A (Additive E)` の組み立て**: `Representation k G V := G →* (V →ₗ[k] V)`
   (mathlib `RepresentationTheory/Basic.lean:50`)。よって
   ```
   ρ : Representation (ZMod p) A (Additive E)
   ρ := { toFun := fun a => (ψ a |> MulEquiv.toAdditive |> AddEquiv.toAddMonoidHom
                              |> AddMonoidHom.toZModLinearMap p),
          map_one' := …, map_mul' := … }
   ```
   `map_one'/map_mul'` は `ψ` が monoid hom かつ各関手が monoid hom 保存なので `simp`/`ext` で閉じる。

> **設計判断 (asModule vs Representation)**: mathlib Maschke の入口は
> `MonoidAlgebra.Submodule.exists_isCompl (p : Submodule k[G] V)` で、`V` が直接 `k[G]`-module
> である必要がある。`Representation` 経由なら `ρ.asModule` (Basic.lean:141; これは `V` そのものの
> 型シノニムに `k[G]`-module 構造を載せたもの) が `k[G]`-module。**最短経路は `ρ.asModule` を取り、
> その上の Submodule に Maschke を適用**。ただし `asModule` は `V` の defeq シノニムなので
> `asModuleEquiv` (Basic.lean:152) で行き来する配管が要る (§2.5 注意)。

### 2.4 ステップ M-d: 与えられた A-submodule `W` を Submodule 化

使用文脈の `W` は `R` の subgroup (`Ω₁(R)⊔S` / `T⊔C` 等) を `mk' S` で `Q` に落とし、
`Ω₁(Q)` (= `E`) の中の subgroup。これを `Additive E` の **Submodule (ZMod p)** にする:

- `W` は `E` の A-invariant subgroup ⇒ `Additive W` は `Additive E` の **AddSubgroup**。
- `ZMod.smul_mem` (ZMod.lean:67) ⇒ ZMod p-加群の AddSubgroup は **自動で scalar 閉** ⇒
  Submodule に昇格できる (`Submodule.mk` の `smul_mem'` を `ZMod.smul_mem` で埋める)。
  **設計判断**: 既存 `AddSubgroup → Submodule` 橋を使う。`Submodule.toAddSubgroup`
  (mathlib `Algebra/Module/Submodule/Basic.lean:127`, GaloisCoinsertion 系) の逆向き。
  探索順: leansearch `"add subgroup to submodule over ZMod"` → なければ `Submodule.mk` 直書き
  (smul_mem' := fun c x hx => ZMod.smul_mem hx c)。

> **needs-impl (軽) M-d-1**: `addSubgroupToZModSubmodule : AddSubgroup M → Submodule (ZMod n) M`
> (M が ZMod n-加群) — `ZMod.smul_mem` で smul_mem' を埋める汎用ヘルパ。
> 1 つ作れば M-d と M-f 両方で使う。**genuine 軽量**。

### 2.5 ステップ M-e: Maschke 呼び出し

```
obtain ⟨Wc, hWc⟩ := MonoidAlgebra.Submodule.exists_isCompl (W_as_submodule)
-- Wc : Submodule (ZMod p)[A] (ρ.asModule),  hWc : IsCompl W_as_submodule Wc
```
`exists_isCompl` (Maschke.lean:162) は `[Field k] [Finite G] [NeZero (Nat.card G : k)]` 下で
任意の `Submodule k[G] V` に補空間を与える。`k=ZMod p` は `[Fact p.Prime]` で体、
`G=A` は `[Finite A]`、`NeZero (Nat.card A : ZMod p)` は §1.2 の coprime から構成 (下記 N-needs)。

> **needs-impl (軽) M-e-1**: `hcop : Coprime |A| |R|`, `p ∣ |R|`, `[Fact p.Prime]`
> ⇒ `NeZero ((Nat.card A) : ZMod p)`。`Nat.Coprime.coprime_dvd_right` + `ZMod.natCast_zmod_eq_zero_iff_dvd`
> + `p ∤ |A|`。**genuine 軽量算術**。`p ∣ |R|` は `IsPGroup p R` + `Nontrivial R` (or 文脈) から。

> ⚠ **`asModule` defeq 配管 (M-e の唯一の落とし穴)**: `Wc` は `ρ.asModule` 上の `(ZMod p)[A]`-submodule。
> 一方 §2.4 で作った `W_as_submodule` は `Additive E` 上の `(ZMod p)`-submodule。
> 両者を同じ `exists_isCompl` の入力にするには **`ρ.asModule` 上の `(ZMod p)[A]`-submodule** に
> 統一する必要がある。`ρ.asModule = Additive E` (defeq) かつ
> `k`-submodule への `restrictScalars` で `(ZMod p)[A]`-submodule ⊇ `(ZMod p)`-submodule の
> 包含が出るが、**A-invariant な subgroup を入れるので `(ZMod p)[A]`-submodule に直接昇格できる**
> (W が A-stable ⇒ `single a 1 • w ∈ W`)。この昇格 (`(ZMod p)`-submodule + A-invariance ⇒
> `(ZMod p)[A]`-submodule) が **M-e の実質作業**。`MonoidAlgebra.single`-scalar の closedness を
> `IsAInvariant` から出す補題が要る (§4 sig の `aInvariantSubmodule`)。

### 2.6 ステップ M-f: complement submodule → subgroup of E → subgroup of Q → subgroup of R

これが親書 §2 N-4 の「**THE HARD PART**」。実際には**3 段の standard 対応の合成**:

1. **submodule → subgroup of E**: `Wc : Submodule (ZMod p)[A] (Additive E)`
   → `Wc.toAddSubgroup : AddSubgroup (Additive E)` (Submodule/Basic.lean:127)
   → `(Wc.toAddSubgroup).toSubgroup`-相当 = `Additive E` の AddSubgroup ⇒ `E` の Subgroup
   (`AddSubgroup (Additive G) ≃ Subgroup G`, mathlib `Subgroup.toAddSubgroup` order iso の逆)。
   呼べる名: `AddSubgroup.toSubgroup` / `Subgroup.toAddSubgroup.symm`。
   結果: `Xc_E : Subgroup E`、A-invariant (Maschke complement が A-stable ⇐ `(ZMod p)[A]`-submodule)。
2. **subgroup of E (= subgroup of `Ω₁(Q)`) → subgroup of Q**: `E = ↥(Omega Q p 1)` なので
   `Xc_E.map (Omega Q p 1).subtype : Subgroup Q`。A-invariance 保存 (subtype が intertwine、
   `restrict_apply_val` @ Ch03:3071 で確認可)。
3. **subgroup of Q (= `R⧸S`) → subgroup of R (S ≤ X)**: `Subgroup.comap (mk' S)`。
   `X := (Xc_Q).comap (QuotientGroup.mk' S)`。`S ≤ X` ∵ `S = ker(mk' S) = comap ⊥ ⊆ comap(anything)`。
   `X⧸S ≅ Xc_Q` ∵ correspondence theorem (`comap_map_eq` 系, QuotientGroup/Basic.lean:353 周辺;
   `S ≤ X` で `map (mk' S) (comap (mk' S) Xc_Q) = Xc_Q`)。
   `X` A-invariant ∵ `φ`-invariant subgroup の `mk'`-comap は `φ`-invariant
   (`quotientMulAutHom_apply` @ Ch04:2274 の intertwine + `comap` 保存)。

> **needs-impl M-f-1〜3 (各々 軽〜中)**: 上 3 段それぞれの「A-invariance 保存」補題。
> いずれも `IsAInvariant` の定義 (`∀a, (φa)•H=H`) を map/comap/subtype で押し引きする配管。
> mmd 依存ゼロ・数学的に自明。**だが本数 (3) があるので個別に sorry-free 化が要る**。

### 2.7 (M) 全体の data flow (1 枚絵)

```
R の subgroup W₀ (=Ω₁(R)⊔S 等, A-inv)
  │ map (mk' S)
  ▼
Q=R⧸S の subgroup, ⊆ Ω₁(Q)=E          φ̄=quotientMulAutHom hS  (Ch04:2248, 既存)
  │ comap (Omega Q p 1).subtype                 │ restrict to E (Ch03:3044, 既存)
  ▼                                              ▼
E の A-inv subgroup W                    ψ : A →* MulAut E
  │ Additive + ZMod.smul_mem (ZMod.lean:67)      │ toAdditive→toZModLinearMap (ZMod.lean:81)
  ▼                                              ▼
Submodule (ZMod p) (Additive E)         ρ : Representation (ZMod p) A (Additive E)
  │ +A-invariance ⇒ (ZMod p)[A]-submodule        │ ρ.asModule = (ZMod p)[A]-module
  ▼─────────────────── Maschke ──────────────────┘
exists_isCompl (Maschke.lean:162) ⇒ Wc : (ZMod p)[A]-submodule complement
  │ toAddSubgroup (Submodule/Basic.lean:127) → Subgroup E  (M-f-1)
  ▼
Xc_E : Subgroup E (A-inv)
  │ map (Omega Q p 1).subtype  (M-f-2)
  ▼
Xc_Q : Subgroup Q (A-inv)
  │ comap (mk' S)  (M-f-3)
  ▼
X : Subgroup R,  S ≤ X,  X⧸S ≅ Xc_Q = complement of W₀⧸S,  X A-invariant   ◀── 返り値
```

---

## 3. feasibility 査定 (candid)

### 3.1 総合: **Tractable / 中**（親書 ⭐⭐ から格下げ）

- **数学的困難はゼロ**。Maschke 本体は mathlib 完成品 (`exists_isCompl`)。Ω₁ の F_p 化も
  A-action の F_p 線形性も商持ち上げも **全て既存ブロック**。残るは**型変換の配管**のみ。
- **作業量の主体**は §2.6 (M-f) の 3 段対応 + §2.5 (M-e) の `(ZMod p)`→`(ZMod p)[A]`-submodule
  昇格 + `asModule`/`asModuleEquiv` の defeq 往復。これらは「証明」というより「正しい補題名を
  当てて ext/simp で潰す」leg work。各 1 補題、計 ~6-8 補題。
- **唯一の真の難所**: `asModule` の defeq シノニム越しの submodule 同定 (§2.5 ⚠)。
  mathlib `RepresentationTheory` に慣れていないと `asModuleEquiv` の `map_smul` 補題
  (Basic.lean:166-177) を正しく使うのに試行錯誤が出る。ここで 1-2 build-cycle 溶ける想定。

### 3.2 工数感 (build-green workflow 前提)

- M-a-1 (Omega abelian ⇒ elementary abelian): 0.5 単位
- M-b (zmodModule 接続): ほぼ既存呼び出し、0.2
- M-c (ρ 組み立て): 0.5 (toAdditive→toZModLinearMap の monoid hom 性 ext)
- M-d-1 (AddSubgroup→ZModSubmodule ヘルパ): 0.3
- M-e-1 (NeZero card): 0.3
- M-e (submodule 昇格 + Maschke 呼び): **1.0** (asModule 配管が重い)
- M-f-1/2/3 (3 段 A-inv 保存): **1.5** (各 0.5)
- 統合 API + 公式補題: 0.7
- **計 ~5 build-green 単位**。0016/§4 v1 と同型の逐次 workflow で 1 セッション圏内。

### 3.3 既知のリスク (技術的)

1. **`asModule` defeq 地獄** (中): `ρ.asModule` は `Additive E` の型シノニムだが、Lean が
   instance を別物と見て `Module (ZMod p)[A]` が `Additive E` 側に降りてこない場面がある。
   `asModuleEquiv` (Basic.lean:152) で明示的に転送し、`asModuleEquiv_symm_map_rho` (Basic.lean:176)
   で `ρ a` ↔ `single a 1 • ·` を繋ぐ。**回避策**: Representation を経由せず、`Additive E` に
   `Module (ZMod p)[A]` を **直接** `MonoidAlgebra.lift`/`Representation.ofModule`-逆で載せる手もあるが、
   `Representation` 経由が定石。実装者は Basic.lean:130-180 を必ず通読。
2. **2 形 Omega の往復** (低): `Omega Q p 1` (closure) と `omega1OfAbelian` の同一視が要る場面。
   abelian で一致するが、補題が無ければ M-a-1 で同時に出す。
3. **`restrict` vs `toMulAutHom` 重複** (低): Ch03:3044 と Ch04:2198 が同義 def 2 本。
   どちらを使っても良いが、本書は **Ch03 `IsAInvariant.restrict`** に統一推奨
   (`restrict_apply_val` simp 補題 @ Ch03:3071 が付属し intertwine 証明が楽)。
   → 別件: この重複は cleanup 候補 (本書 §6 参照)。

---

## 4. 提案 signature (将来実装用、exact)

### 4.1 中核 API: 一般 A-invariant complement (single source, 複製防止)

`new file`: `/home/ywr/odd-order/OddOrder/BG/Ch1_Preliminary/OperatorMaschke.lean`
(module `OddOrder.BG.Ch1_Preliminary.OperatorMaschke`、import `OddOrder.Isaacs.Ch04_Commutators.Main`
+ `OddOrder.GroupTheory.{PRank,OmegaSubgroup}` + `Mathlib.RepresentationTheory.Maschke`)。
親書 N-4 IMPORT 制約 (Ch03/04 が GroupTheory を import するので GroupTheory には置けない) を遵守。

```lean
namespace OddOrder.BG.Ch1_Preliminary

open OddOrder.GroupTheory OddOrder.Isaacs.Ch03 OddOrder.Isaacs.Ch04

/-- **N-4 Maschke bridge (中核)**: `φ : A →* MulAut R`, `(|A|,|R|)` coprime, `p` prime,
`S` A-invariant normal で商 `R⧸S` が abelian。`Ω₁(R⧸S)` を `F_p[A]`-加群と見て、
A-invariant subgroup `W₀ ≤ R` (`S ≤ W₀`, `W₀⧸S ⊆ Ω₁(R⧸S)`) の像に対する
**A-invariant complement** を **`R` の subgroup `X`** (`S ≤ X`) として返す。

返り値の性質:
* `S ≤ X`
* `IsAInvariant φ X`
* `(X⧸S の像) ⊓ (W₀⧸S の像) = ⊥` かつ `⊔ = Ω₁(R⧸S)` (complement; `mk' S` の image で書く)。 -/
theorem exists_aInvariant_complement_in_omega1_quotient
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (hR : IsPGroup p R)
    {A : Type*} [Group A] [Finite A] {φ : A →* MulAut R}
    (hcop : Nat.Coprime (Nat.card A) (Nat.card R))
    {S : Subgroup R} [S.Normal] (hS : IsAInvariant φ S)
    (hQab : ∀ x y : R ⧸ S, x * y = y * x)                       -- R⧸S abelian
    {W₀ : Subgroup R} (hSW : S ≤ W₀) (hWinv : IsAInvariant φ W₀)
    (hWΩ : (W₀.map (QuotientGroup.mk' S)) ≤ Omega (R ⧸ S) p 1) :  -- W₀⧸S ⊆ Ω₁(R⧸S)
    ∃ X : Subgroup R, S ≤ X ∧ IsAInvariant φ X ∧
      IsCompl ((X.map (QuotientGroup.mk' S)) ⊓ Omega (R ⧸ S) p 1)
              (W₀.map (QuotientGroup.mk' S))
        -- ⊓ Ω₁ は X⧸S を Ω₁ に切り落とす (X 自体は Ω₁ 越えてよい); 実装で要詰め
```

> **設計判断 (返り値の complement 表現)**: `IsCompl` を `Ω₁(R⧸S)` の lattice 内で取る形。
> `X⧸S` が `Ω₁` を超える場合があるので `⊓ Omega` で切る。**ここを `True`/`∃X, S≤X` だけに
> 弱めるのが最大の scaffold-trap (§5)**。最終形 (complement を `Submodule.IsCompl` で持つか
> subgroup `IsCompl` で持つか) は実装時に使用側 (Thm 4.12 a-3) の需要で詰める。
> 実装者は **complement の 2 条件 (⊓=⊥, ⊔=Ω₁) を必ず field 化**せよ。

### 4.2 使用側の薄い特殊化 (Thm 4.12 a-3 / 4.16 B-2 が直接呼ぶ形)

中核を **`W₀ := Ω₁(R) ⊔ S` (a-3) / `T ⊔ C` (B-2)** で特殊化。これは別 theorem ではなく
中核に引数を入れて呼ぶだけ (純ラッパー禁止規約 §ラッパー方針: **薄い特殊化は書かず使用側で直接呼ぶ**)。
→ Thm 4.12/4.16 本体内で `exists_aInvariant_complement_in_omega1_quotient` を直接適用。

### 4.3 補助 (M-f 配管, 中核証明内で使う private 補題群)

```lean
/-- ZMod n-加群上の AddSubgroup は自動で Submodule (scalar 閉; `ZMod.smul_mem`). -/
private def addSubgroupToZModSubmodule {n : ℕ} {M : Type*} [AddCommGroup M] [Module (ZMod n) M]
    (H : AddSubgroup M) : Submodule (ZMod n) M

/-- A-invariant subgroup of E ⇒ (ZMod p)[A]-submodule of (Additive E). -/
private def aInvariantToMonoidAlgebraSubmodule … : Submodule (ZMod p)[A] (Additive E)

/-- (ZMod p)[A]-submodule ⇒ A-invariant subgroup of E (逆向き, complement 取り出し用). -/
private def monoidAlgebraSubmoduleToAInvariantSubgroup … : {H : Subgroup E // IsAInvariant ψ H}

/-- φ-invariant subgroup の mk'-comap は φ-invariant (M-f-3). -/
private theorem isAInvariant_comap_mk' {S X̄ : …} (hX̄ : IsAInvariant (quotientMulAutHom hS) X̄) :
    IsAInvariant φ (X̄.comap (QuotientGroup.mk' S))
```

---

## 5. SCAFFOLD-TRAP 監査 (本件固有)

親書 §0 の総論「Doneness = hypothesis constructibility, NOT sorry-count」を本件に特化:

| 罠の形 | 具体 | genuine な回避 |
|---|---|---|
| **(最重要) 持ち上げの再発明 sorry** | 実装者が `quotientMulAutHom` (Ch04:2248) を **見落とし**、`letI : MulAut (R⧸S) := sorry` や `MulAction A (R⧸S) := sorry` を書く | **§0 表を最初に読む**。商持ち上げは既存。restrict も既存。新規 instance を sorry で作らない |
| **complement を `∃X, S≤X` に弱める** | 返り値を「S を含む A-inv subgroup が在る」だけにし、**complement 性 (⊓=⊥, ⊔=Ω₁) を落とす** | §4.1 の `IsCompl` 2 条件を field 化。`True` 禁止 |
| **`W₀⧸S ⊆ Ω₁` を仮定で逃げる** | `hWΩ` を ⊤ で埋められず放置 | 使用文脈 (Ω₁(R)⊔S や T⊔C) で `hWΩ` を**実際に構成**できることを確認してから中核を呼ぶ |
| **`NeZero (|A|:ZMod p)` を hoist** | `[NeZero (Nat.card A : ZMod p)]` を **追加仮説**にして Maschke を通すが、coprime から導かない | M-e-1 を sorry-free で。`hcop` + `p∣|R|` から **実証** |
| **abelian ⇒ elem ab を仮定** | `(hEab : IsElementaryAbelian p ↥(Omega Q p 1))` を仮説に積む | M-a-1 を sorry-free で。abelian + Omega 特徴付けから |
| **Maschke を自前 sorry で代替** | mathlib `exists_isCompl` の型合わせが面倒で `sorry : ∃ complement` と書く | `MonoidAlgebra.Submodule.exists_isCompl` (Maschke.lean:162) を**必ず経由**。型合わせは §2.5 配管で |

**最終判定基準**: 実装後、`exists_aInvariant_complement_in_omega1_quotient` を
**`#print axioms` で確認**し、かつ **「すべての仮説引数 (`hcop`/`hS`/`hQab`/`hSW`/`hWinv`/`hWΩ`)
が使用文脈 (Thm 4.12 a-3) で `sorry` 無しに供給できる」**ことを目視確認するまで **未完**とする。
特に `hWΩ` と `hQab` は使用側で本物が要る (a-3 では `R'≤S` ⇒ `hQab`、`Ω₁(R)⊔S` ⇒ `hWΩ`)。

---

## 6. 副次観測 (cleanup 候補, 本件スコープ外)

- **`IsAInvariant.restrict` (Ch03:3044) と `IsAInvariant.toMulAutHom` (Ch04:2198) が同義 def 2 本**。
  body もほぼ同一 (toFun/invFun/left_inv/right_inv/map_mul' が一致)。片方を消し他方へ集約すべき
  (CLAUDE.md ラッパー方針: 同事実 2 名で証明分裂を避ける)。本件は Ch03 版に統一して進める。
- 親書 §2 N-4 の本文「商持ち上げが repo に無い (genuine needs-impl)」記述は **stale**。
  `quotientMulAutHom` 実装後の状態を反映していない。親書を更新するなら N-4 を
  「lift は済、残りは Maschke bridge のみ」に書き換えるのが正確。

---

## 7. 参照パス (絶対, 全て確認済)

- **本書親**: `/home/ywr/odd-order/notes/bg/s04_prop411_thm416_design.md` (§2 N-4, §4.2 a-3, §5.5 B-2)
- **商持ち上げ (既存)**: `/home/ywr/odd-order/OddOrder/Isaacs/Ch04_Commutators/Main.lean`
  - `quotientMulAutHom` 定義 = **L2248**
  - `quotientMulAutHom_apply_mk'` (`@[simp]`, 公式 `φ̄(a)[g]=[(φa)g]`) = **L2266**
  - `quotientMulAutHom_apply` = **L2274**
  - `actionCommutator_quotient_eq_map` = L2282
  - `IsAInvariant.toMulAutHom` (restrict 重複) = **L2198**
- **制限作用 (既存)**: `/home/ywr/odd-order/OddOrder/Isaacs/Ch03_SplitExtensions/Main.lean`
  - `IsAInvariant.restrict` = **L3044**, `restrict_apply_val` (`@[simp]`) = **L3071**
  - `IsAInvariant` 定義 = L2894, `.smul_mem` = L2898, `.inv_smul_mem` = L2920
  - `IsAInvariant.of_characteristic` = **L2950** (Omega.characteristic ⇒ φ-inv)
- **Ω₁ / Agemo (既存)**: `/home/ywr/odd-order/OddOrder/GroupTheory/OmegaSubgroup.lean`
  - `Omega` 定義 = L59, `Omega.characteristic` (instance) = **L89**
  - `omega1OfAbelian` = L190, `mem_omega1OfAbelian` = L208
- **zmodModule (既存)**: `/home/ywr/odd-order/OddOrder/GroupTheory/PRank.lean`
  - `IsElementaryAbelian.zmodModule` = **L83** (`[NeZero p]`)
  - `IsElementaryAbelian.card_eq_pow_finrank` = L102, `.log_card_eq_finrank` = L119
- **IsElementaryAbelian (既存)**: `/home/ywr/odd-order/OddOrder/GroupTheory/ElementaryAbelian.lean:41`
- **Maschke (mathlib)**: `.lake/packages/mathlib/Mathlib/RepresentationTheory/Maschke.lean`
  - `MonoidAlgebra.Submodule.exists_isCompl` = **L162** (`[Field k][Finite G][NeZero (Nat.card G:k)]`)
  - `MonoidAlgebra.exists_leftInverse_of_injective` = L145
  - instance `IsSemisimpleModule k[G] V` = L168
- **Representation (mathlib)**: `.lake/packages/mathlib/Mathlib/RepresentationTheory/Basic.lean`
  - `Representation := G →* (V →ₗ[k] V)` = **L50**
  - `asModule` = L141, `asModuleEquiv` = L152, `asModuleEquiv_symm_map_rho` = L176
- **ZMod 線形 (mathlib)**: `.lake/packages/mathlib/Mathlib/Algebra/Module/ZMod.lean`
  - `ZMod.map_smul` (加法準同型は ZMod n-線形) = **L62**, `ZMod.smul_mem` = **L67**
  - `AddMonoidHom.toZModLinearMap` = **L81**, `toZModLinearMapEquiv` = L90
  - `AddCommGroup.zmodModule` = **L44**
- **MulEquiv→AddEquiv (mathlib)**: `.lake/packages/mathlib/Mathlib/Algebra/Group/Equiv/TypeTags.lean:42`
  (`MulEquiv.toAdditive`)
- **Submodule↔AddSubgroup (mathlib)**: `.lake/packages/mathlib/Mathlib/Algebra/Module/Submodule/Basic.lean:127`
  (`Submodule.toAddSubgroup`)
- **QuotientGroup.congr (mathlib)**: `.lake/packages/mathlib/Mathlib/GroupTheory/QuotientGroup/Defs.lean:391`
  (quotientMulAutHom の内部で使用)
- **correspondence (mathlib)**: `.lake/packages/mathlib/Mathlib/GroupTheory/QuotientGroup/Basic.lean:353`
  (`comap_map_eq` 周辺, M-f-3 の `X⧸S≅Xc_Q`)
- **新規作成先**: `/home/ywr/odd-order/OddOrder/BG/Ch1_Preliminary/OperatorMaschke.lean`
