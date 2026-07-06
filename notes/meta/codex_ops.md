# Codex 運用メモ (codex レーン専用)

> **配置の理由 (hub 裁定 2026-07-06, ユーザー承認 option 1)**: 以下は **codex 固有の sandbox 運用**であり、
> Claude レーン・hub には無関係。全 agent がロードする `CLAUDE.md`(共有 governance doc)に置くと非 codex
> レーンの context コストになるため、codex 専用の本ファイルに切り出す。**codex は起動時に LAUNCH.md 経由で
> 本ファイルを参照**。Claude レーン/hub は本ファイルを読む必要はない。内容は codex commit `3d96b94a` の保全
> (成果を無駄にせず軌道修正 = CLAUDE.md「進捗の測り方」保全原則)。

## Codex sandbox 運用 (読み取りコマンド)

Codex managed sandbox では、未承認の単純な読み取りコマンド (`ls`/`readlink`/`sed`/一部 `git` plumbing 等) が
実行前に `bwrap: loopback: Failed RTM_NEWADDR: Operation not permitted` で落ちることがある。これはリポジトリの
問題ではなく sandbox 起動経路の問題なので、**失敗してから同じコマンドを retry する運用を避ける**。

- ファイル内容検索・抜粋はまず `rg` を使う (`rg -n -C`, `rg -n "" file` など)。`cat | head` や `rg | head`
  のような pipe/chain は避け、必要なら `rg` の pattern/context/max-output で絞る。
- 繰り返し使う読み取り系で sandbox failure が予想されるものは、**初回から** `require_escalated` + 狭い
  `prefix_rule` で実行し、以後の同系コマンドを通す。典型: `ls -l`, `readlink`, `git ls-files`,
  `git rev-list --count`, `sed -n`, `lake build <target>`。
- 承認 prefix は必要最小限にする。`python`/`bash -lc`/heredoc/redirect 付きコマンド/破壊的コマンドを広く承認しない。
- merge 前後の確認 (`git status`, `git diff`, `git rev-list --count HEAD..main`) は、sandbox で落ちるものを
  失敗させてから再実行するのでなく、既知なら最初から上記の狭い approval を使う。
- `apply_patch` も sandbox helper 経路で同じ `bwrap` failure を起こす場合がある。その場合だけ、理由を明示して
  権限付きの単発編集コマンドに切り替える (恒久 prefix は付けない)。
