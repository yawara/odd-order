# 9208 — 可換群の冪核 Ω / 冪像 ℧ 部分群 (特性 + 位数積)

**claim**: lane a (9200 band) / **状態**: landing 済 (2026-07-26)

## 目的

`OddOrder/GroupTheory/AbelianPowerSubgroups.lean` (新 leaf, `OddOrder.lean` 配線済)。
可換群 `Q` (`[Group Q] [IsMulCommutative Q]`) の

* `powKernel Q n = {x | x ^ n = 1}` (= `p`-群での `Ω_i`, `n = p ^ i`)
* `powImage Q n = {x ^ n | x}` (= `℧^i`)

を `n` 乗準同型 `powHom Q n : Q →* Q` の核・像として定義し、**特性部分群 instance** と
**`|Ω_n| · |℧_n| = |Q|`** (第一同型定理) を与える。

## 既存との関係 (着手前検索の結果)

* `OddOrder/GroupTheory/OmegaSubgroup.lean` の `omega1OfAbelian G H p hH` は
  **ambient `Subgroup G` に landing する形** (`H : Subgroup G` + 可換性の Prop)。
  `Subgroup ↥H` 側の `Ω`/`℧` は無く、特性部分群 instance も無い。用途が異なるので併存させる。
* mathlib の `powMonoidHom` は `CommMonoid` を要求するので `↥(P : Subgroup G)` には直接使えない
  (`CommGroup` を `letI` すると `Subgroup.toGroup` との instance diamond)。
  **`IsMulCommutative` mixin を使うと diamond が起きない** — 本 leaf の設計の要点。

## 内容

| 名前 | 内容 |
|---|---|
| `powHom` | `n` 乗写像 (`Commute.mul_pow` で準同型) |
| `powKernel` / `powImage` | `ker` / `range` |
| `powKernel_characteristic` / `powImage_characteristic` | instance |
| `card_powKernel_mul_card_powImage` | `|Ω_n| · |℧_n| = |Q|` |
| `powImage_mul_le` / `powKernel_le_mul` | 単調性 |
| `powImage_le_powKernel` | `Ω_{mn} = ⊤ ⇒ ℧_m ≤ Ω_n` |
| `powKernel_two_pow_mul_eq` | ⭐ 不動点: `Ω_{2n} = Ω_n ⇒ Ω_{2^k·n} = Ω_n` |

## 消費点

Isaacs Problem 5C.3 (issue 1055): 可換 Sylow-2 が位数 `2^5` なら初等可換。
`|Ω₁|` と `|℧¹|`, `|℧²|` の位数勘定で「指数 2 の特性部分群対」を作り Problem 5C.2
(`card_eq_two_of_characteristic_relIndex_eq_two`) に流し込む。
