# Tasaki 本形式化の再設計・再実装方針

## Status / Decision

- Status: **review-ready proposal (complete-reset revision)**。PR merge 前なので accepted
  ではないが、bootstrap を止める未決 P0 は残していない。以下の decision set 全体を
  この PR で review する。
- 対象: Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
  (Springer, 2020) の形式化を、保存された旧 `main` とは別の再実装系列で
  front-to-back に作り直す。
- 基準 revision: `01bcb49d49db92c225cfa74b74d409dd0a9c4edc`
  (`main` の 2026-09-15 時点の tip)。本書中の測定値は、特記しない限りこの
  revision で得た。
- この設計 PR の変更範囲は本ファイルだけである。現行 Lean source、tests、CI、TeX、
  catalogue、依存 manifest の reset は、設計承認後の atomic bootstrap PR で行う。

本提案の decision は次の通りである。

1. 旧 `main` は履歴・比較・証明アイデアを読むための **frozen legacy** として残す。
   新系列に旧公開 API との互換性は要求しない。
2. 設計承認後の atomic bootstrap PR で、旧 `LatticeSystem/**`、tests、root aggregator、
   `formalization-status/**`、旧 scripts/checkers/workflows、legacy anchor 由来の `tex/**`、旧
   docs/site/history/catalogue を全面削除する。既存 code は一切 carry-forward、import、cherry-pick しない。
   path を再利用する場合も内容は scratch rewrite とする。
3. 新系列は、無限頂点型上の graph と有限 volume を分離し、有限 volume の
   configuration/operator を一つだけ定義する。
4. 有限次元 operator の canonical representation は `Matrix` とする。
   `Module.End` 等への bridge は spectral API の境界一箇所に閉じ込める。
5. spin-half と general spin、有限系と将来の無限体積系を、コピーではなく同じ
   kernel の特殊化・制限として構成する。
6. Tasaki の atomic source claim を印刷順に進める。旧実装の進捗地点や救出しやすさを理由に
   §2.5、Chapter 4、Hubbard 等へ先回りしない。
7. 旧 proof は仕様でも依存でもなく、legacy anchor から読む参考資料にすぎない。新系列へ
   旧 code を一行も移植せず、旧 axiom も一括移植しない。
8. 数学実装を始める前に、本書全体の source census を完了し hash-lock する。Chapter 2--11、
   Appendix A、Solutions pp. 493--520 の named result/problem/definition/conjecture、全番号付き
   数式、番号のない proof obligation、同一箇所に並ぶ独立結論を **atomic claim** として
   個別に対象とする。Chapter 1、references、index 等も
   `out_of_scope` page として census に残し、無言で読み飛ばした page を作らない。
9. 計算上の canonical operator は `Matrix`、物理 observable は Hermitian 証明を持つ
   `Observable` bundle とする。zero vector を eigenvector と呼ばない。
10. volume inclusion、configuration restriction、operator の identity extension、volume
    equivalence による reindexing は、identity/composition law まで初期 API に含める。
11. weighted coupling の support は「non-edge なら weight zero」、実際に非零な辺からなる
    graph を `activeGraph` と定義する。connectivity と sign は `activeGraph` 上の refinement
    bundle に置く。
12. fermion は finite configuration/operator carrier だけを共有する。bosonic `embedSite` を
    fermion operator の API として共有せず、Chapter 9 到達時に ordered Jordan--Wigner 表現を
    canonical とする。
13. bootstrap は一つの atomic PR とし、削除と fresh minimal root/lake/CI/checkers/
    blueprint を同時に成立させる。trunk には途中の壊れた commit を置かない。
14. 未実装 atomic claim は metadata blueprint で `inventoried` / `catalogued` として保持する。
    source claim ID と implementation slice ID を別 namespace にし、番号付き数式、番号のない
    proof obligation、独立結論のそれぞれに個別の binding、content digest、status、phase
    eligibility を持たせる。slice はそれらの ID の順序付き集約であり、それ自身を一個の
    `ItemStatement` や status 正本にしない。`...Statement : Prop → proof` lifecycle は assertion
    disposition だけに適用する。definition/notation は declaration と必要 law、hypothesis/domain
    は consumer の binder/metadata、conjecture/out-of-scope は非 proof terminal として別 lifecycle
    を持つ。derived assertion は parent terminal 後の `consequence` と current proof frontier に
    必要な `prerequisite` を排他分類する。production/repository に `sorry` theorem stub または
    temporary axiom を置かない。
15. project axiom は空の `LatticeSystem/Axioms/**` から始め、専用 path/namespace、閉じた分類、
    exact environment check の下でのみ追加できる。project axiom が空の result だけを
    `proved`、依存する result を `proved-relative`、axiom 自身を `approved-deferred` とする。
16. Tasaki §2.1 の `S=1/2,1,...` は source assertion のまま保持し、`N : ℕ` kernel の `N=0` は
    別 `consequence` derived assertion とする。basis は `m(k)=N/2-k`、matrix は
    row=output/column=input とする。
17. legacy status/docs/TeX の複製は捨てるが、新系列の公開数学 docs/TeX は禁止しない。書誌・
    claim registry・Lean environment を正本とし、docs/TeX は claim ID と locator を参照して
    数学変更 PR と同時同期する。
18. warning-as-error/standard linter とは別に、private を含む全 project declaration の doc
    comment を `docBlame` / `docBlameThm` / `#lint` 相当で CI gate する。

この文書の承認は設計の承認であり、旧 source の数学的正当性や移植可否を一括承認する
ものではない。

## Goals

- Tasaki の本文、定理、問題、必要な式を front-to-back に追える source-oriented な
  形式化を作る。
- 公開 theorem の statement が、証明経路ではなく本文の数学的対象と最弱仮定を表す
  ようにする。
- underlying combinatorial datum を graph とし、頂点型自体には有限性を組み込まない。
- 同じ有限 volume kernel を spin、fermion、将来の局所 observable に再利用できる
  ようにする。
- theorem/proof、source locator、actual axiom set、status の関係を一意にする。
- 全巻 atomic source claim を実装前に列挙し、未実装が不可視になる余地をなくす。
- 小さい import surface と一方向の dependency DAG を保つ。
- `lake build` warning zero、`sorry` / `admit` / `native_decide` 不在を継続する。
- 強い仮定を置く theorem について、仮定の同時充足可能性と結論の非空虚性を確認する。
- 無限体積極限を長期目標として保持しつつ、Chapter 2 より先に C\*-algebra framework を
  作り込まない。

## Non-goals

- 旧 namespace、declaration name、import path の互換維持。
- 旧 source/test/checker/status catalogue/site/history/TeX の複製を「ひとまず」残すこと。
- 旧 source を新しい directory へ機械的に移動すること。
- 旧 catalogue の全行を新 status ledger へ機械的に移すこと。
- 旧 proof-stage module を順番に「きれいにする」漸進 refactor。
- `sorry` theorem や temporary axiom を backlog 表現として使うこと。
- legacy status を複製した TeX proof guide や、Lean/blueprint と独立に進捗を手編集すること。
  新系列の人間向け公開数学 docs/TeX は non-goal ではなく、数学内容を公開する PR で同期する。
- Tasaki 本で現在必要のない Lieb、Miyao、別文献の独立形式化。
- 二つ目の具体的利用がない一般化や、将来便利そうという理由だけの helper。
- Chapter 2 の bootstrap 時点で quasi-local algebra、KMS、GNS、thermodynamic limit を
  完成させること。
- 旧実装と同じ declaration 数、file 数、証明方針を再現すること。

## Evidence-backed diagnosis

### 規模と形状

基準 revision には Lean file が 1,727 個、合計 287,519 行ある。working tree の変化に
左右されない再測定は、revision を archive した一時 directory 上で行う。

```sh
revision=01bcb49d49db92c225cfa74b74d409dd0a9c4edc
measure_dir=$(mktemp -d)
git archive "$revision" LatticeSystem | tar -x -C "$measure_dir"
find "$measure_dir/LatticeSystem" -name '*.lean' | wc -l
find "$measure_dir/LatticeSystem" -name '*.lean' -print0 | xargs -0 wc -l | tail -1
```

`LatticeSystem/Quantum/SpinS/` 直下だけで 873 file、
`LatticeSystem/Fermion/JordanWigner/Hubbard/` 直下で 369 file ある。

```sh
find "$measure_dir/LatticeSystem/Quantum/SpinS" -maxdepth 1 -name '*.lean' | wc -l
find "$measure_dir/LatticeSystem/Fermion/JordanWigner/Hubbard" -maxdepth 1 -name '*.lean' | wc -l
```

開発工程に由来する名前を持つ file は、dev-research の広義分類では約 186 file だった。
名称の分類境界に依存するため、この値自体を gate にはしない。同じ revision で、狭義の
`Core|Structural|Wrapper|Assembly|Capstone|Discharge|Conditional` は 143 file、
`Bridge|Final|Target|Endpoint|Step` まで含める広義再測定は 188 file である。

```sh
find "$measure_dir/LatticeSystem" -name '*.lean' \
  | awk '$0 ~ /(Core|Structural|Wrapper|Assembly|Capstone|Discharge|Conditional)/' \
  | wc -l
find "$measure_dir/LatticeSystem" -name '*.lean' \
  | awk '$0 ~ /(Core|Structural|Wrapper|Assembly|Capstone|Discharge|Conditional|Bridge|Final|Target|Endpoint|Step)/' \
  | wc -l
rm -rf "$measure_dir"
```

数値そのものより、`Core`、`Structural`、`Bridge`、`Capstone` 等が数学的責務ではなく
当時の proof stage を表し、その stage が恒久 import graph に残っていることが問題である。

### spin-half / general-spin の重複

`LatticeSystem/Quantum/ManyBody.lean` は

```lean
abbrev ManyBodyOp (Λ : Type*) :=
  Matrix (Λ → Fin 2) (Λ → Fin 2) ℂ
```

と `onSite` を定義する。一方、
`LatticeSystem/Quantum/SpinS/MultiSiteCore.lean` は

```lean
abbrev ManyBodyOpS (Λ : Type*) (N : ℕ) :=
  Matrix (Λ → Fin (N + 1)) (Λ → Fin (N + 1)) ℂ
```

と `onSiteS` を定義する。off-site agreement、pivot configuration、異なる site の
可換性、加法・scalar・adjoint の証明も両系列に重複する。spin-half は local basis
`Fin 2` を一般 local basis に代入すれば得られるため、二本の kernel は不要である。

### `SpinS/Operators.lean` の basis-action 解釈の誤り

`LatticeSystem/Quantum/SpinS/Operators.lean` の raising/lowering の **entry 定義と係数**は、
列 `j` を入力 ket、行 `i` を出力 ket と読む `Matrix.mulVec` convention に整合する。一方で
同 file 末尾の `spinSOpPlus_apply_top` は `Fin.last N` **行**が zero であることを証明して
「最高 weight state を annihilate」と説明し、`spinSOpMinus_apply_bottom` は `0` **行**が
zero であることを「最低 weight state を annihilate」と説明している。basis convention
`m(k) = N/2 - k` では最高 weight は `k = 0`、最低 weight は `k = N` であり、state の
annihilation を表すのはそれぞれ `S⁺` の `0` **列**、`S⁻` の `N` **列**である。したがって
これら二 lemma は成り立つ row-zero statement ではあっても、名前と doc comment の物理解釈は
誤っている。後続の `LadderBoundary.lean` が用いる column lemma とは区別しなければならない。

これは legacy declaration を「証明済みだから採用」と判定できない具体的な negative evidence
である。新系列では raising/lowering の係数、`Fin (N+1)` の基底順、matrix-entry formula だけを
Tasaki 本文と再照合して採用候補にし、この endpoint lemma の名前・row/column 解釈・説明は
drop する。basis action は `mulVec` と basis vector に対する column statement を主契約とし、
row statement を導く場合は row と明記する。

### graph と finite volume の切断

`LatticeSystem/Lattice/Graph.lean` が `SimpleGraph Λ` 自体に `[Fintype Λ]` を要求しない
判断は正しい。しかし有限量子系は `Λ` 全体に `[Fintype Λ]` を要求し、無限体積系は
`LatticeSystem/Quantum/SpinS/InfiniteVolumeGroundState.lean` の別構造
`InfiniteSpinSystem` から始まる。無限 graph 上の有限 `Finset` volume、induced graph、
volume restriction を共有する中間層がない。

また Hamiltonian 側の主要 API は生の `J : Λ → Λ → ℂ` を受け、real、star-fixed、
symmetric、nonnegative、zero diagonal、support、strict positivity 等を theorem ごとに
再度要求する。`couplingOf` は uniform weight の薄い関数であり、model invariant を
bundle していない。このため、例えば Theorem 2.4 系の公開 signature に coupling の
実装詳細が多数露出する。

### theorem statement への proof route の流出

`LatticeSystem/Quantum/SpinS/AnisotropicHeisenbergSpinSTheorem24.lean` の capstone は、
coupling の複数条件、diagonal shift、MLM/toy Hamiltonian 用 scalar、sector 非空性、
balanced-sector bookkeeping、既存 theorem package を平坦な引数として受ける。
declaration name も `...of_MLM_casimir_ladder_t23_pf_general` のように証明経路を表す。

基準 revision の最新修正 `01bcb49d` は、7 module に 30 個あった固定 `c` による
全 `lam D` 一様上界という充足不能 binder を削除した。この修正は 11 file、
425 insertions / 172 deletions で、回帰 fixture
`LatticeSystem/Tests/AxisSwapDiagBoundSatisfiable.lean` だけで 305 行ある。

```sh
git show --stat --oneline 01bcb49d49db92c225cfa74b74d409dd0a9c4edc
git show 01bcb49d49db92c225cfa74b74d409dd0a9c4edc:\
LatticeSystem/Tests/AxisSwapDiagBoundSatisfiable.lean | wc -l
```

これは個別の失敗だけでなく、巨大 signature、positional forwarding、proof-stage API、
signature fixture が組み合わさると、数学的 defect の修正より周辺維持の方が大きくなる
ことを示す。

### import root と test の役割過多

`LatticeSystem.lean` は公開 API を選ぶ facade ではなく、library import DAG の全 tip を
列挙することを自ら invariant としている。基準 revision では 103 imports ある。
`LatticeSystem/Tests.lean` は 187 test modules を手動列挙し、tests 全体は 26,827 行ある。

```sh
revision=01bcb49d49db92c225cfa74b74d409dd0a9c4edc
git show "$revision":LatticeSystem.lean | rg -n '^import ' | wc -l
git show "$revision":LatticeSystem/Tests.lean | rg -n '^import ' | wc -l
measure_dir=$(mktemp -d)
git archive "$revision" LatticeSystem/Tests | tar -x -C "$measure_dir"
find "$measure_dir/LatticeSystem/Tests" -name '*.lean' -print0 | xargs -0 wc -l | tail -1
rm -rf "$measure_dir"
```

proof 自身を再掲する signature shim、grep hit 数、過去の一時 signature を保つ fixture は、
数学的意味の regression test と分離されていない。

### axiom と status の堆積

基準 revision で行頭 `axiom ` を raw text 検索すると 81 hit するが、そのうち 11 hit は
module/doc comment 内の prose である。Lean declaration としての project axiom は **70 個**
である。11 個の false positive は次の file:line で、revision-pinned な grep 出力を全件
目視分類した。

- `GeneralFlatBandDisconnected.lean:119`
- `MielkeIncidenceMatrix.lean:375`
- `MielkeTheorems.lean:100`
- `SpinWaveExcitation.lean:24`
- `AnisotropicHeisenbergSpinSLambdaOneBoundary.lean:191`
- `AnisotropicHeisenbergSpinSObligation2FromSU2Unique.lean:36`
- `AnisotropicHeisenbergStrictGSAtSU2FromStrictGap.lean:16`
- `BoxLocalTranslationInvariant.lean:19`
- `BulkDensity.lean:14`
- `NoLongRangeOrder1D.lean:25`
- `ShastryNoSSBReduction.lean:371`

```sh
revision=01bcb49d49db92c225cfa74b74d409dd0a9c4edc
git grep -n '^axiom ' "$revision" -- 'LatticeSystem/**/*.lean'
# raw 81 - comment false positives 11 = project axiom declarations 70
```

C\*-algebra、GNS、KMS 等の合意済み defer 対象だけでなく、後で discharge するための
定理、物理的 marker predicate、有限次元の未完部分が同じ構文で混在する。新系列で
これらを一括移植すると、古い分類判断まで無批判に固定してしまう。

現行 governance では `docs/formalization/legacy/` が complete status / capstone の暫定
authority であり、prototype の `formalization-status/v2/` は全体 authority ではない。
しかし theorem claim、locator、declaration name、axiom status は Lean source、legacy
catalogue、`tex/proof-guide.tex`、一部の structured records に反復され、同期漏れで drift
する。現行 validator の厳密な actual-axiom 照合という発想は採用するが、複数の status
正本と legacy catalogue guard は採用しない。

## Adopt / Rewrite / Drop inventory

### Adopt: 判断または検証手法として採用

| 資産 | 採用する部分 | 条件 |
|---|---|---|
| `lakefile.toml` | pinned mathlib revision、`relaxedAutoImplicit = false`、warning-as-error、標準 linter、long-file check という判断 | file は scratch rewrite し、最小構成で再確認する |
| `lean-toolchain`, `lake-manifest.json` | reproducible toolchain と pinned dependency | この二つだけは内容を保持し、dependency 更新を混ぜない |
| `Lattice/Graph.lean` | graph に有限性を埋め込まない判断、path/cycle/hypercubic との接続 | API は新 `Geometry` 層で再記述する |
| `SpinS/Operators.lean` | basis `Fin (N+1)`、`m(k)=N/2-k` の順序、raising/lowering の係数と entry formula | source と再照合し、新 canonical API 上で証明し直す。末尾 endpoint lemma の誤名・row/column 解釈は採用しない |
| `ManyBody.lean`, `MultiSiteCore.lean` | configuration basis 上の site embedding と可換性の数学的アイデア | generic local basis 一本に統合する |
| `Math/MatrixAnalysis/` 等 | source-neutral な有限次元線形代数の proof idea | 実際の次 theorem に必要、mathlib に同等物なし、最弱仮定を満たすものだけ |
| tests の具体的手法 | `Fin n` の全ケース証明、small matrix の全 entry 計算、二つの独立定義の等式 | 意味を検査する短い test に限定 |
| status validator | actual axiom set と declaration module を Lean 環境から検査する発想 | 旧 script は削除し、environment-based checker を最小から作り直す |
| Tasaki の書誌・locator | 1st ed., Springer 2020 の chapter/section/equation/page | tracked citation metadata に保持し、gitignored file を build/review の前提にしない |

低層資産は file 単位で採用しない。採用単位は「定義の数学的内容」「証明アイデア」または
「検証方法」であり、新系列の source は原則として書き直す。旧 code を直接 import せず、
commit や file を cherry-pick しない。各 implementation-slice PR は adopt gate の各項目について
`adopt / rewrite / drop` と根拠を PR 内の legacy assessment に記録する。

### Rewrite: 数学的目的を保ち、表現を変更

| 現行対象 | 書き直し方 |
|---|---|
| `ManyBodyOp` / `ManyBodyOpS` | `Config Λ I` / `Op Λ I` と generic `embedSite` に一本化 |
| `spinSOp1/2/3` 群 | `Axis` indexed `spinOp` を中心にし、`S±` を導出 |
| 生の `J` と仮定列 | graph と edge coupling invariant を一つの構造へ bundle |
| `Bool` sublattice marker | 公開面は explicit bipartition witness、内部だけ必要なら Bool bridge |
| `Matrix.toLin'` の反復 | `Spectrum` 境界に `eigenspace` / `groundSpace` を定義 |
| 巨大 existential/conjunction capstone | `GroundState`、`GroundSpace`、sector 等の数学的 named definitions を使用 |
| finite/infinite の別系統 | 無限 `V` 上の `Finset V` volume と restriction から接続 |
| source status | 一つの machine-readable ledger と生成表示へ縮約 |
| theorem-oriented helper 名 | 数学的対象・作用・性質を表す名前へ変更 |

### Drop: 新系列へ持ち込まない

- 旧 declaration/import path の compatibility shim と deprecated alias。
- facade を旧 path に残すための `Core.lean` 分割。
- `Structural`、`Wrapper`、`Assembly`、`Discharge`、`Conditional` 等の proof-stage 分割。
- PR ごとの新 module。
- theorem の statement を再掲するだけの test。
- grep 数、line number、一時 signature を仕様化する test。
- legacy catalogue の手移植と旧 roadmap の PR chronicle。
- `docs/` の旧 site/history/catalogue/limitations/roadmap と、手編集 status を複製する site generator。
- legacy `tex/` の status/proof-guide 複製と旧 TeX workflow/reference。新系列で source claim を
  解説する公開数学 docs/TeX とその同期・生成 workflow まで禁止するものではない。
- `formalization-status/` と旧 status/schema/retirement/cutover machinery。
- 旧 scripts/checkers および release/pages/update workflow。
- 参照ゼロの decorative helper と、将来便利そうという理由だけの一般化。
- 旧 axiom の一括移植。
- 本文より強いが証明を通しやすい仮定。

## Target dependency DAG and directory layout

依存方向は次に固定し、逆向き import と chapter の先取り import を禁止する。

```text
Mathlib
  ↓
LatticeSystem.Math       LatticeSystem.Geometry
             \             /
              Quantum.Finite
                    ↓
               Quantum.Spin
                    ↓
                  Models
                    ↓        ↘
                    │      Axioms (approved assumptions only)
                    │        ↓
          Tasaki2020.ChapterNN
                    ↓
            Tests / StatusChecks
```

`Blueprint` は Lean dependency graph の外側にある immutable source inventory であり、Lean
declaration への binding だけを持つ。`Axioms` は foundation/model を import してよいが、
foundation/model から `Axioms` への逆 import は禁止する。chapter result は必要な axiom module
だけを直接 import し、axiom umbrella import は作らない。

初期 directory 案は次の通りである。file は PR 単位ではなく数学的責務で分ける。

```text
LatticeSystem/
  Axioms/                     # bootstrap 時は空。承認済み分類だけを後から作る
    OperatorAlgebra/
    FunctionalAnalysis/
    Symmetry/
  Math/
    ...                         # 要求された時だけ追加
  Geometry/
    Graph.lean
    Volume.lean
    Hypercubic.lean
  Quantum/
    Finite/
      Configuration.lean
      Operator.lean
      SiteEmbedding.lean
      Spectrum.lean
    Spin/
      Basis.lean
      Operators.lean
      Algebra.lean
      Rotation.lean
      ManyBody.lean
      MagnetizationSector.lean
  Models/
    Heisenberg/
      Definition.lean
      Ferromagnet.lean
      Antiferromagnet.lean
  Tasaki2020/
    Chapter02/
      Section01.lean
      Section02.lean
      Theorem21.lean
      Theorem22.lean
      ...
  Tests/
    Quantum/
    Tasaki2020/
blueprint/
  schema.json
  tasaki-2020/
    source-index.json
    bindings/
references/
  tasaki-2020.json            # 書誌・edition・source hash metadata のみ
docs/
  math/                       # 新系列の人間向け公開数学解説（必要になった時に追加）
tex/
  tasaki-2020/                # 公開数学文書の TeX source（必要になった時に追加）
```

`LatticeSystem.lean` は stable public surface だけを import する。全 leaf/tip coverage は
build target が担い、root file の責務にしない。atomic claim の追加ごとに file を作る必要は
なく、同じ数学的責務で 700 行未満を目安に育てる。分割は責務が二つになった時に行う。
本の本文、PDF、抽出 text、statement の大量引用は tracked しない。tracked に置くのは書誌、
locator、hash、formalization に必要な数学的 restatement だけである。

### Single source of truth and public mathematical documents

旧 `docs/formalization/legacy/`、旧 status site、`tex/proof-guide.tex` のように同じ claim/status を
複数箇所へ手入力する構成は廃止する。しかしこれは新系列の人間向け公開数学 docs/TeX を永久に
禁止する決定ではない。新しい数学内容を実装・変更する PR は、`CLAUDE.local.md` の公開
ドキュメント同期規律に従い、必要な `docs/math/**` と `tex/tasaki-2020/**` を同じ PR で更新する。
公開 TeX/doc comment には文献名、edition、節・定理/式番号、printed page と PDF page、claim ID
を明記する。

重複を避ける正本と生成/参照関係は次に固定する。

- 書誌、edition、page mapping、source fingerprint の正本は `references/tasaki-2020.json`。
- source locator、atomic restatement、source-order、claim/slice membership の正本は claim registry
  (`blueprint/tasaki-2020/source-index.json` と binding shard)。
- assertion が `typed` になった後の形式 statement の正本は claim ID に bind された唯一の Lean
  `...Statement` declaration、その proof/axiom dependency の正本は Lean environment である。
  definition/notation の正本は bind された Lean declaration、hypothesis/domain の正本は bind
  された consumer binder、conjecture/out-of-scope の正本は disposition-specific registry record
  であり、存在しない `Statement` / proof binding を要求しない。
- atomic status、frontier、slice/chapter 集計は上記 registry/binding/environment から生成する。
  docs/TeX に手編集 status table を置かない。表示する場合は generated region/artifact とし、
  stale generation を CI が reject する。
- 人間向け docs/TeX は数学的動機・定義・証明案内を著述してよいが、claim ID を参照し、式や
  theorem の canonical restatement を再定義しない。checker は参照 ID、locator、binding digest
  を照合する。数学 API/claim/proof を変えた PR は対応する公開説明も同期する。

bootstrap 時点で数学解説がまだ無ければ `docs/math/` / `tex/tasaki-2020/` を空で作る必要はない。
ただし closed-tree policy は manifest に登録された新系列の公開 docs/TeX と、その生成・検証
tooling を許容し、後続 PR での追加を設計変更扱いにしない。TeX compiler 等の dependency は
既存の project-local/reproducible 環境だけを使い、追加が必要なら別の明示的 dependency 変更とする。

## Canonical types

以下は意図を示す sketch であり、この設計 PR では Lean 宣言を追加しない。

### Infinite vertices and finite volumes

```lean
variable {V : Type*}

abbrev Volume (V : Type*) := Finset V
```

`SimpleGraph V` と model data には `[Fintype V]` を要求しない。有限計算は
`Λ : Finset V` の subtype `↥Λ` で行う。有限 graph theorem が全頂点を扱う場合だけ
局所的に `[Fintype V]` と `Λ = Finset.univ` を用いる。

この境界により、将来 `V = ℤ`、`V = Fin d → ℤ` としたまま `Λₙ : Finset V` を増大させ、
同じ local Hamiltonian を制限できる。

volume API は包含 `h : Λ ⊆ Ω` と volume equivalence を一級データとして扱い、少なくとも
次を持つ。

- `restrictConfig h : Config Ω I → Config Λ I`: configuration の座標制限。
- `restrictGraph Λ G`: `G` の `↥Λ` への induced graph。
- `restrictCoupling Λ J`: graph/coupling の finite volume への制限。
- `extendOp h : Op Λ I → Op Ω I`: `Ω \ Λ` 上で恒等作用する tensor-factor identity
  extension。matrix entry は outside-`Λ` の configuration が一致しない時に zero とする。
- `reindexConfig` / `reindexOp`: volume/basis equivalence による添字変更。

次の law を定義と同時に証明する。

- restriction の identity と composition。
- identity extension の identity と composition
  (`extendOp (Λ ⊆ Θ) = extendOp (Ω ⊆ Θ) ∘ extendOp (Λ ⊆ Ω)`)。
- `extendOp` が zero/one/add/mul/scalar/adjoint を保つこと。
- reindexing の identity、inverse、composition と、restriction/extension との自然性。
- `Observable` の identity extension/reindexing が Hermitian 性を保つこと。

ket の `Λ → Ω` extension は outside-`Λ` の基準状態を選ばなければ canonical でないので、
初期 API には置かない。「operator の identity extension」と「configuration の restriction」を
混同しない。

### Generic local basis and Matrix canonical representation

```lean
abbrev Config (Λ : Finset V) (I : Type*) := ↥Λ → I
abbrev Ket (Λ : Finset V) (I : Type*) := Config Λ I → ℂ
abbrev Op (Λ : Finset V) (I : Type*) :=
  Matrix (Config Λ I) (Config Λ I) ℂ
```

必要な箇所で `[Fintype I] [DecidableEq I]` を置く。site embedding は一つだけ持つ。

```lean
def embedSite (Λ : Finset V) (x : ↥Λ) (A : Matrix I I ℂ) : Op Λ I := ...
```

spin-half は `I = Fin 2`、spin `S = N/2` は `I = Fin (N+1)` である。heterogeneous local
basis は Chapter 2 の要求ではないため初期 kernel には入れない。二つ目の実需要が出た時に
generalize する。

`Matrix` を canonical とする理由は、Tasaki の基底表示、entry sign、Perron--Frobenius、
small finite computation が主経路だからである。linear map/eigenspace が必要な時は
`Quantum.Finite.Spectrum` に一度だけ bridge を定義し、公開 theorem が毎回
`Matrix.toLin'` を展開しないようにする。`Matrix` と `Module.End` の双方を正準 API に
しない。

計算 carrier と物理 observable は区別する。

```lean
structure Observable (Λ : Finset V) (I : Type*) where
  toMatrix : Op Λ I
  isHermitian : toMatrix.IsHermitian

def IsEigenvector (A : Op Λ I) (ψ : Ket Λ I) (μ : ℂ) : Prop :=
  ψ ≠ 0 ∧ A.mulVec ψ = μ • ψ
```

Hamiltonian、spin component、number operator 等、self-adjoint であることが数学的契約に
含まれる対象は `Observable` を返す。途中計算と非 self-adjoint な raising/lowering/
creation/annihilation は `Op` のまま扱う。`Observable` の add、real scalar、commuting mul、
unitary conjugation、identity extension は Hermitian 証明込みの constructor とする。

`Quantum.Finite.Spectrum` だけが matrix-to-linear-map bridge を所有し、次を公開する。

- `eigenspace A μ`
- Hermitian observable の実固有値列
- `groundEnergy H : ℝ`
- `groundSpace H`
- `IsGroundState H ψ := IsEigenvector H.toMatrix ψ (groundEnergy H)`

`IsEigenvector` は必ず `ψ ≠ 0` を含み、zero vector を eigenvector/ground state と呼ぶ API は
作らない。公開 theorem は `Matrix.toLin'`、固有値の並べ方、最小 index の実装を露出しない。
必要な `[Nonempty (Config Λ I)]` 等は `Spectrum` の constructor 境界で解決する。

### Spin representation

- Tasaki §2.1 が置く source domain **`S = 1/2, 1, 3/2, ...`** は一つの source claim として
  そのまま census/binding に保持し、kernel の parameterization に合わせて無言で `S = 0` を
  本文へ混入させない。
- 実装 kernel は `N : ℕ`、`S = N/2` とする。`N = 0` の一-dimensional trivial representation
  まで同じ定義と代数則が成立することは便利な **derived assertion claim** であり、Tasaki source claim
  とは別の derived-claim ID、`consequence` role、`derived_from` edge、statement digest、binding、
  status を持たせる。
- local basis は `SpinBasis N := Fin (N+1)`。
- basis convention は明示的に **`m(k) = N/2 - k`** とし、`k = 0` が highest weight、
  `k = N` が lowest weight である。matrix は row=output、column=input と読み、basis action と
  ladder endpoint は column statement で検査する。
- axis は `Axis` で indexed にする。
- `spinOp N : Axis → Matrix (SpinBasis N) (SpinBasis N) ℂ` を中心に置く。
- `spinRaise` / `spinLower`、Casimir、rotation はこの API から導く。
- `S=1/2`、`S=1` の行列を別定義せず、一般定義の specialization theorem にする。

### Bundled coupling

公開 theorem が次を個別引数として反復しない構造を用意する。base structure は概念的に
次の形で確定する。

```lean
structure WeightedCoupling (V : Type*) where
  graph : SimpleGraph V
  weight : V → V → ℝ
  symm : ∀ x y, weight x y = weight y x
  zero_of_not_adj : ∀ {x y}, ¬ graph.Adj x y → weight x y = 0
```

`SimpleGraph` の irreflexivity と `zero_of_not_adj` から diagonal zero を導く。
`graph` は許容 support の supergraph であり、zero-weight edge は interaction を結ばない。
したがって

```lean
(J.activeGraph).Adj x y ↔ J.graph.Adj x y ∧ J.weight x y ≠ 0
```

と定義する。support の意味は **non-edge implies zero** であり、graph edge 上の nonzero を
base structure に要求しない。connectivity theorem は `J.graph.Connected` ではなく
`J.activeGraph.Connected` を要求する。

nonnegative/strictly-positive antiferromagnetic coupling、nonpositive/strictly-negative
ferromagnetic coupling、bipartite support は `activeGraph` 上の refinement bundle とする。
符号 convention は refined constructor で一度固定し、各 theorem に real/symmetric/support/
sign/connectivity を平坦に再掲しない。

Hamiltonian の正準定義は有限 induced `activeGraph` の unordered edge sum とする。
ordered-pair sum と `1/2` は theorem の本文がその表記を必要とする時の bridge に限定する。

positivity を coupling の全用途へ強制しない。例えば ferromagnetic/antiferromagnetic の
符号は model layer の refined structure とする。

### Fermion representation boundary

fermion は `Config` / `Ket` / `Op` という有限 matrix carrier と volume/reindexing machinery
だけを共有する。異なる site の operator が可換であることを契約に含む bosonic
`embedSite` を fermionic creation/annihilation の構成 API として共有しない。

Chapter 9 に到達した時、有限 mode に明示的な linear order を持たせ、ordered
Jordan--Wigner string を canonical concrete representation とする。CAR はその表現から
証明する。一般 graded tensor product、抽象 CAR algebra、order-independent equivalence は、
Tasaki の現在の atomic source claim が実際に必要とするまで導入しない。fermion のために Chapter 2 の
kernel を先に複雑化しない。

### Named mathematical predicates

以下を用意し、巨大な conjunction と representation detail を capstone から隠す。

- nonzero を含む `IsEigenvector`
- `Observable` 上の `groundEnergy` / `groundSpace` / `IsGroundState`
- `MagnetizationSector`
- explicit bipartition / connected weighted graph predicate

bundle は仮定を隠して弱く見せるためではなく、同じ invariant 集合を一度構成し、すべての
consumer が同一の数学的対象を受け取るために使う。constructor の充足可能性 test も行う。

## Axiom policy

1. `sorry`、`admit`、`native_decide`、未証明 theorem stub、temporary axiom を禁止する。
2. 旧 project axiom declaration 70 個は一つも自動移植しない。bootstrap 後の
   `LatticeSystem/Axioms/` は空から始める。
3. primitive vocabulary は axiom ではなく `structure` / `def` で表す。内容のない predicate
   も、命題を真とする証拠を与えない限り `def ... : Prop` とする。
4. axiom の許可 taxonomy は、`OperatorAlgebra/{CStar,State,GNS,KMS}`、
   `FunctionalAnalysis/WeakDual`、`Symmetry/Wigner` に閉じる。`Misc`、`Temporary`、`TODO`、
   chapter 名を category にしてはならない。Wigner も有限次元で証明可能な形は証明する。
5. cluster expansion、quasi-adiabatic continuation、Lieb--Robinson bound、一般の
   Rellich--Kato 型分岐連続性など、真に作用素環的・解析的極限を要する対象であっても、
   現在の許可 taxonomy のどれかへ無理に分類してはならない。将来それらが current frontier
   で必要になった時は、独立 design PR で数学的境界、専用 category/path、許可する declaration
   範囲、reopen condition、CI rule を review し、closed taxonomy への追加が承認されるまで
   axiom 化できない。現在許可される taxonomy は第4項の列挙だけである。
6. **無限体積、難しさ、実装量、有限次元であることは axiom category でも defer 理由でもない。**
   無限グラフ、volume exhaustion、極限の存在・性質は長期中心目標として証明する。
   その途中で上記の許可 taxonomy に該当する個別 component だけを、宣言単位で
   defer 審査する。
7. 有限次元・固定 finite volume の線形代数、spectral theory、固有値連続性、縮退摂動、
   変分評価は必ず証明する。「難しい」「摂動論」「後で使う」は defer 理由にならない。
8. conjecture は `def ... : Prop` として statement を記録してよいが、true と主張する
   `axiom` を置かない。
9. axiom declaration は分類に対応する `LatticeSystem/Axioms/**` path と
   `LatticeSystem.Axioms.*` namespace の中だけに置く。axiom umbrella module は作らず、
   consumer は必要な module だけを直接 import する。foundation/model は `Axioms` を
   import してはならない。
10. deferred declaration には stable axiom ID、source locator、exact statement、category、
    欠けている数学、consumer obligations、承認 PR、reopen condition を registry に記録する。
11. CI は Lean environment の全 project axiom と registry を双方向完全一致で検査し、binding
    された全 declaration の expected/actual axiom set も完全一致で検査する。path/namespace
    違反、未登録 axiom、存在しない登録、axiom set の過不足、`sorryAx` を reject する。
12. project axiom dependency が空の result だけを `proved`、非空で完全一致する result を
    `proved-relative`、axiom declaration 自身を `approved-deferred` と生成表示する。
    `proved-relative` を chapter の axiom-free 完了数へ算入しない。
13. 大型 theorem は proved supporting lemma の列へ分割し、未証明 capstone を source に
    置かない。

## Atomic claim, implementation slice, PR, and test policy

### Atomic claim and implementation slice

coverage census は Tasaki 1st ed. (Springer, 2020) の全 page を対象とする。Chapter 2--11、
Appendix A、Solutions pp. 493--520 では、全 named Definition / Theorem / Lemma /
Proposition / Corollary / Conjecture / Problem、全番号付き数式、番号のない proof obligation、
一つの result 内の複数の独立結論を登録する。heading や節を一個の巨大 item にせず、番号付き
数式一つ、unnumbered obligation 一つ、独立に真偽を問える結論一つを atomic claim の上限とする。
一つの番号付き数式が独立な複数の等式・結論を列挙する場合も claim を分け、同じ printed
number と subclaim key を locator に持つ。Chapter 1、front matter、references、index 等も
page record を作り `out_of_scope` disposition とする。zero-item page も明示し、読んだ page と
未監査 page を区別する。

local text 抽出から得た約 194 named-heading candidate と約 1,283 equation-token candidate は
機械 seed でしかない。抽出方法により equation token は約 1,287 とも数えられるため、どちらも
完成件数として固定しない。printed page と PDF page の二 locator、候補から disposition への
対応、solution locator を人手で一巡し、fresh な独立 reviewer が page-by-page に二巡目を行う。
unresolved candidate、未分類 equation/unnumbered obligation/independent conclusion、未監査 page
がゼロになった時だけ source index を hash-lock する。

ID namespace は次の二つを混同しない。

- **source claim ID** (`TASAKI2020-CLAIM-...`): 本文に実在する atomic claim。source-order key、
  edition、section、printed/PDF page、equation/theorem/problem number、subclaim key、restatement、
  disposition を持つ。
- **derived claim ID** (`LATTICE-DERIVED-...`): kernel の一般化・境界 case・bridge law など、
  本文の直接 claim でない独立結論。derived assertion は必ず dependency role
  `consequence` または `prerequisite` のちょうど一方を持ち、前者は `derived_from`、後者は
  `required_by` edge を持つ。source coverage 件数には数えない。
- **implementation slice ID** (`TASAKI2020-SLICE-...`): review/実装の便宜上、source/derived claim
  ID を source order に並べた順序付き list。slice は claim ではなく、独自の statement
  declaration、binding、digest、手編集 status、frontier position を持たない。slice status は
  member claim の状態から生成する集約表示にすぎない。

claim ID は append-only とする。誤登録も削除・再利用せず tombstone と `superseded_by` を残す。
source disposition は `assertion`、`definition`、`notation`、`hypothesis`、`domain`、`conjecture`、
`out_of_scope` に閉じる。`independent_claim`、`restatement`、`proof_step`、`equation`、`obligation`
は `assertion` の subkind であり、別 lifecycle を暗黙に作らない。`derived_claim` は disposition
ではなく上記の別 ID namespace に置き、同じ disposition のいずれかを必ず持つ。

全 claim record は locator、source-order key、disposition、normalized content、`content_digest`、
binding、status、phase eligibility を個別に持つ。`statement_digest` を全 disposition に要求せず、
disposition 別 lifecycle を次に固定する。

| disposition | binding / digest | generated lifecycle | proof frontier |
|---|---|---|---|
| `assertion` | 唯一の Lean `...Statement : Prop` と `statement_digest`、proof declaration、actual axiom set、non-vacuity obligation | `inventoried → catalogued → typed → proved` または `proved-relative` / `approved-deferred` | source assertion のみ eligible |
| `definition` | Lean `def` / `structure` / `abbrev` と `declaration_digest`、actual axiom set、必要 law の assertion claim ID list | `inventoried → catalogued → declaration-bound`。law が無ければ `definition-implemented`、必要 law が全て proof-terminal なら `definition-implemented-with-laws` | ineligible。consumer assertion の非 frontier dependency |
| `notation` | notation/syntax declaration、展開先、`declaration_digest`、展開先 declaration の actual axiom set、必要 law claim ID list | `inventoried → catalogued → declaration-bound → notation-implemented`。law があれば全 law terminal を要求 | ineligible。consumer assertion の非 frontier dependency |
| `hypothesis` / `domain` | consumer claim ID、binder 名・型・量化位置の `binder_digest` | `inventoried → catalogued → binder-bound` | ineligible。consumer assertion の非 frontier dependency |
| `conjecture` | normalized statement の `content_digest`。型検査が必要なら証拠を与えない `def ... : Prop` だけを任意 binding | `inventoried → catalogued → conjecture-recorded` | permanently ineligible。proof/axiom binding 禁止 |
| `out_of_scope` | page/range、理由、`metadata_digest` | `inventoried → out-of-scope-recorded` | permanently ineligible。Lean binding 禁止 |

definition/notation の law は同じ record 内の手書き checkbox で済ませず、独立した source/derived
`assertion` claim ID として通常の statement/proof lifecycle を通す。hypothesis/domain record は
真であることを証明する claim ではなく、どの consumer のどの binder が原典の仮定・量化域を
表すかを検査する。外部文献に証明を委ねる assertion も消さず、新 axiom policy に従って
prove/defer を判断する。

初期 blueprint は metadata と数学的 restatement だけを持つ。frontier は slice でなく、
**proof-eligible source assertion ID だけ**から `statement_frontier`（最古の未 `typed` assertion）と
`proof_frontier`（最古の未 proof-terminal assertion）を計算する。definition/notation/
hypothesis/domain は current assertion が必要とする非 frontier dependency として直前に実現し、
conjecture/out-of-scope は source-order gate 上で disposition-specific terminal に記録する。
後の source assertion へ進むには、それ以前の全 record が各 disposition の required state を
満たさなければならない。derived assertion の eligibility は dependency role ごとに分ける。

- **`consequence`**: 一つ以上の `derived_from` parent が全て required terminal に到達した後だけ
  `typed/proved` eligible。parent の結果として後から得る claim であり、source proof の前提には
  できない。
- **`prerequisite`**: `required_by` target がその時点の current **source proof frontier assertion**
  と一致し、その target が `typed`、かつ target の final line から backward-chain した証明上の
  必要性が review 済みの場合だけ先行して `typed/proved` eligible。全 prerequisite は target を
  root とする非巡回 DAG をなし、target またはその proof に依存してはならない。future/past source
  claim、単なる便利 helper、statement 構築だけを理由とする先行は reject する。

どちらも source assertion frontier の位置を持たず、完了しても frontier を進めない。一つの
derived assertion に両 role/edge を許さず、checker は role/edge cardinality、target=current
frontier、parent terminal、DAG acyclicity を environment dependency と registry の双方から検査する。
ここで target=current は prerequisite の **最初の状態遷移時の base proof frontier** に対する
条件である。registry は target、base frontier key、承認済み dependency digest を immutable に
記録し、target 完了後は current でなくなっても履歴を再検証して completed prerequisite を保持する。

必要な型が実装済みになってから、realization PR は `assertion` claim ごとに次のような
declaration を build する。

```lean
/--
Tasaki 2020, 1st ed., §2.4, Theorem 2.1, printed p. 35.
Claim: `TASAKI2020-CLAIM-C02-S04-THM-2.1`.
-/
def Theorem21Statement : Prop := ...
```

同じ theorem に三つの独立 assertion があれば三つの claim ID と三つの `...Statement` を置き、
conjunction 一個で一括 binding しない。この段階は `typed` であり、真とは主張しない。別の proof PR でだけ
`theorem theorem21 : Theorem21Statement := by ...` を追加して `proved` に進める。
assertion binding は **claim ID ごとに** claim declaration、proof declaration、module、statement digest、
expected logical/project axiom set、non-vacuity declaration を結ぶ。proof theorem の型が対応
claim と definitionally equal でなければ CI failure とする。他 disposition は上表の binding を
個別に検査する。claim ごとの status は binding と Lean environment から生成し、phase eligibility
も claim ごとに検査する。

全 theorem を `sorry` で先置きする案は statement を型検査できる利点があるが、未証明 result
を downstream が利用でき、`sorryAx` を theorem として存在させ、後半章の型を作るために全
architecture を早期固定する。metadata → built `Prop` → proof の分離は、全 target の可視性を
保ちつつ未証明命題を証拠として利用不能にするため、`sorry` stub より強い。

status field は人が書かない。claim registry、binding、Lean environment から上表の
disposition-specific status を atomic claim ごとに生成する。slice/chapter の status は atomic
status の順序付き集約から生成する。derived assertion の表示は status とともに role、eligibility
parent/target、frontier-history key を必ず示し、`typed/proved` だけで先行可否を隠さない。tracked
prose を第二の status 正本にしない。

### PR unit and frontier

- 通常は一つの implementation slice について realization PR と assertion proof PR を分離してよいが、
  PR 内でも binding/digest/status/phase eligibility は atomic claim ごとに独立させる。
- realization PR は必要な definition/notation declaration、hypothesis/domain binder binding、
  conjecture/out-of-scope record、および assertion ごとの built `Statement : Prop` と source
  equivalence/non-vacuity 計画までを含み、assertion の result theorem を含まない。
- proof PR は assertion ごとの凍結済み statement を変更せず、直前から backward-chain した必要補題、result、
  semantic test、environment verification を完結させる。
- 大型 theorem だけ、同じ theorem issue の中で複数 PR に分割できる。各 PR はそれ自体で
  axiom-free な一つの数学結果を完成させ、最終 theorem のどの step に必要かを明記する。
- PR 分割の都合で `Core` / `Bridge` / `Final` file を増やさない。
- unrelated refactor、将来用 helper、別 chapter の準備を混ぜない。
- capstone 実装前に、本文との statement review と hypothesis audit を独立に行う。
- source-order 上の source-assertion statement/proof frontier を越えて遷移しない。同じ slice の
  後続 assertion も、先行 assertion が同 phase の required state を満たした後でだけ typed/proved
  に進める。非 assertion member は consumer 前に disposition terminal/required state を満たす。
  一つの atomic PR で contiguous な複数 member を進める場合、checker は base からの遷移を
  member 順に simulation し、gap/skip を reject する。現在の source proof frontier assertion の
  final line から必要な Appendix dependency と `prerequisite` derived assertion だけ、上記
  `required_by` / acyclic-DAG rule の下で先行できる。`consequence` は先行不可である。
- 旧 code を import または cherry-pick しない。proof idea を読む場合も、新 canonical API
  上で source から実装し直す。
- 各 slice PR に claim 別の `Legacy assessment` を置き、参照した旧 declaration ごとに
  `adopt idea / rewrite / drop`、adopt gate の判定、直接 code 移植がないことを記録する。

### Adopt gate for an old declaration

旧 declaration の内容を再利用するには、次をすべて満たす。

1. source locator と本文 statement を再照合した。
2. 本文より強い仮定がない。
3. 仮定の同時充足可能性を具体 model または独立 consistency argument で確認した。
4. 結論が vacuous でない。
5. actual axiom set が新 policy に合う。
6. 現 atomic claim の final line からの backward chain 上にある。
7. 新 canonical type 上で自然に表現できる。
8. mathlib または新 kernel と重複しない。
9. proof-route 名でなく数学的な名前を持つ。
10. statement review または小さい semantic test がある。

一項でも落ちたものは修理移植ではなく、本文 statement から再構成する。判定結果は当該
slice PR の claim 別 `Legacy assessment` に残し、設計 PR で旧資産全体を事前承認しない。

### Test policy

- Lean proof 自身が theorem の第一の test である。
- 別 test は、small finite exhaustive、matrix entry、definition bridge、non-vacuity、過去に
  実際に起きた semantic regression のいずれかを検査する時だけ追加する。
- public theorem の型を `example := theoremName ...` で再掲する signature shim は、外部 API
  freeze を明示的に決めた対象以外では使わない。
- grep hit 数、file 行番号、proof helper 名、一時的な引数順を test invariant にしない。
- 強い bundle/refined structure には concrete constructor witness を置く。
- 強い theorem hypothesis には、可能なら最小非自明 graph/model で positive control を置く。
- false/unsatisfiable hypothesis を導入しないため、quantifier order と parameter dependence を
  statement review で明示する。

### Per-PR verification

1. 対象 module の局所 build。
2. 全 module を含む `lake build`、warning zero。public root から未 import でも build する。
3. 専用 doc-comment gate。public/private を含む全 project declaration を environment から列挙し、
   `docBlame` / `docBlameThm` / `#lint` 相当で doc comment 欠落を error にする。
   `mathlibStandardSet` と `warningAsError` だけで代用しない。
4. `sorry` / `admit` / `native_decide` / `sorryAx` 不在。
5. Lean-bound assertion/definition/notation declaration の actual logical/project axiom set の完全
   一致確認。hypothesis/domain/conjecture/out-of-scope に存在しない proof axiom set を要求しない。
6. source locator、disposition-specific binding/digest/status/phase eligibility。assertion ではさらに
   claim/proof binding と proof type の definitional equality。
7. dependency-layer 違反、import cycle、unregistered/orphan declaration がゼロ。
8. semantic test と non-vacuity witness。強い hypothesis に witness がない例外は理由と独立承認を要求。
9. source index と base branch の diff に対する disposition-aware state/source-assertion-frontier
   monotonicity check。derived assertion について consequence parent terminal、prerequisite target が
   その状態遷移時の base current proof frontier、role/edge 排他、dependency DAG 非巡回、完了後の
   immutable eligibility history も検査する。
10. public math docs/TeX の claim ID・書誌・定理/式番号・printed/PDF page・digest 参照と generated
    status region が同期していること。数学内容に影響しない PR は no-sync 理由を記録する。
11. cold/warm のどちらかを明記した compile-time delta と import 増分の記録。

### Anti-regression gates

base branch と PR head の machine-readable diff で、次を default reject する。

- atomic claim の削除、stable claim ID の再利用、tombstone の復活、source claim ID と slice ID
  の混同、slice member の無承認並べ替え。
- disposition-specific terminal、`proved` / `proved-relative` / `typed` からの無承認 downgrade。
  assertion の proof、definition/notation declaration、hypothesis/domain binder binding、terminal
  metadata record の消失。
- locator、disposition、`content_digest` または disposition-specific digest の silent change。
- semantic weakening、すなわち仮定の強化、結論の弱化、量化域の縮小、または同等の適用範囲・
  内容の後退。source 誤読訂正であっても旧 atomic claim を tombstone/supersession し、訂正根拠を
  dedicated statement-change PR で独立 review するまでは reject する。
- assertion statement change と proof change の同居。definition/notation declaration change と
  dependent law proof change の同居。
- expected project axiom set の拡大、`proved` から `proved-relative` への silent change。
- source-assertion frontier より後の assertion の状態遷移、非 frontier dependency でない
  definition/notation/binder の先行実装、source-order の変更。
- derived assertion の role/edge の silent change、両 role 併記、`consequence` の parent-terminal
  前進行または parent proof からの利用、`prerequisite` の target が遷移時 current proof frontier
  でない先行、dependency cycle、target proof 後に追加された未承認 prerequisite。
- active binding の declaration 不在、未登録 public result、build 対象外 module。

base diff は `content_digest` と disposition-specific digest の一致/不一致を機械判定する。
assertion の statement digest が不一致なら変更方向にかかわらず通常 PR を止め、dedicated
statement-change PR、既存 proof result の一時除去、`typed` への戻し、独立 source-equivalence
review を要求する。その review で仮定の強化・結論の弱化・
量化域縮小等を semantic regression と分類し default reject する。仮定の弱化、結論の強化、
量化域拡大等も digest change であり同じ専用 PR と review を必須とするが、それだけを理由に
semantic regression とは分類しない。semantic foundation の definition を変える場合は
dedicated breaking-foundation PR とし、Lean constant dependency graph による transitive impact
closure、影響する全 statement/result、semantic tests、full build を提示する。proof PR と
混ぜない。definition/notation/binder/metadata digest の変更も dedicated disposition-change PR と
dependent assertion の impact closure を要求する。

`rewrite-main` は protected branch とし、direct push と force push を禁止する。build、census、
layer、environment axiom、全 declaration doc-comment、public math docs/TeX sync、monotonicity check
を required にし、realization PR は独立 disposition/source-equivalence review、assertion proof PR は
独立 verification review を required にする。人間向け status は常に生成物で、
手編集可能な `proved` label を正本にしない。

## Migration sequence

### R0: legacy freeze and design update

- 旧 `main` の anchor は
  `01bcb49d49db92c225cfa74b74d409dd0a9c4edc` とし、frozen legacy とする。
- 再実装 trunk は **`rewrite-main`** とする。`rewrite-main` は上記 anchor から派生し、
  履歴比較可能性を保つ。
- `redesign/tasaki-reimplementation-plan` を `rewrite-main` への設計 PR とする。
- 本 PR は本ファイルだけを追加し、現コードを変更しない。
- complete reset、closed keep allowlist、complete census、state machine、Axioms isolation、
  anti-regression gate を一つの矛盾のない設計として承認し、未決 P0 をゼロにする。

### R1: atomic complete-reset bootstrap

設計承認後の一つの bootstrap PR で、次を全面削除する。

- 旧 `LatticeSystem/**` production/tests と `LatticeSystem/Tests.lean`
- 旧 root tip aggregator `LatticeSystem.lean`
- `formalization-status/**` と旧 status/schema/retirement/cutover machinery
- 旧 `scripts/**`、checkers、site generators
- legacy `tex/**` と旧 TeX tooling/workflow/reference（特に status/proof-guide の複製）
- `docs/**` の旧 site/history/catalogue/limitations/roadmap と手編集 status generator
- release/pages/update を含む旧 workflows

bootstrap 後に旧内容を保持してよい closed allowlist は `lean-toolchain` と
`lake-manifest.json` の pinned toolchain/dependency 内容だけである。`.gitignore`、`README.md`、
`lakefile.toml`、`LatticeSystem.lean`、CI path を再利用する場合も scratch rewrite とする。
承認済み本設計は root `DESIGN.md` へ移す。legacy `docs/` / `tex/` の内容は残さないが、
新系列の public math docs/TeX は manifest 登録された path として後から追加可能であり、directory
自体を永久禁止しない。新しい tracked tree は概念的に次へ閉じる。

```text
.github/CODEOWNERS
.github/workflows/lean_action_ci.yml
.gitignore
DESIGN.md
README.md
LatticeSystem.lean
blueprint/schema.json
blueprint/tasaki-2020/source-index.json
lake-manifest.json
lakefile.toml
lean-toolchain
references/tasaki-2020.json
scripts/check_blueprint.py
scripts/check_closed_tree.py
scripts/check_layers.py
scripts/check_lean_environment.lean
scripts/check_doc_comments.lean
scripts/check_public_math_docs.py
scripts/fixtures/                 # checker の tracked positive/negative fixtures
```

source directory と binding shard は、最初に実需要が出た PR でこの allowlist に manifest-driven
に追加する。allowlist 外の legacy path/file が残れば bootstrap CI を落とす。この PR は
「削除だけ」を一時的に merge して後続 PR で直す二段階にしない。同じ PR の最終 tree で次を
同時に成立させる。

- package identity、`lean-toolchain`、依存を変えない最小 `lakefile.toml` / manifest。
- public root `LatticeSystem.lean`。DAG tip aggregator ではなく、bootstrap 時点の空の stable
  surface を表す。
- default build target と、checker を含む CI target。
- import layer rule を検査する dependency-free checker。
- empty blueprint から開始できる atomic-claim/slice schema、closed-tree check、layer check、
  actual-axiom checker、disposition-aware base-diff/source-assertion-frontier monotonicity check。
  schema/checker は derived assertion の `consequence` / `prerequisite` role、排他的 edge、parent
  terminal、遷移時 target=base current proof frontier、immutable eligibility history、dependency
  DAG acyclicity を初期状態から扱う。
- `mathlibStandardSet` / `warningAsError` とは別に、全 build 対象 module の environment を走査し、
  public/private を含む全 project declaration へ `docBlame` / `docBlameThm` / `#lint` 相当を
  適用する `check_doc_comments`。欠落 doc comment は CI error とし、private helper も例外にしない。
- public math docs/TeX がまだ空でも実行でき、後続追加時に claim ID、書誌、定理/式番号、
  printed/PDF page、binding digest、generated status region を照合する generic
  `check_public_math_docs`。R3 で bootstrap infrastructure を追加・修理せず同期 check を使える
  よう、schema と pass/fail fixture を R1 で完成させる。
- `README.md` の最小 project identity、build command、legacy anchor、新 trunk の説明。
- tracked `references/tasaki-2020.json` に edition、ISBN/DOI、chapter/section/page range、
  source fingerprint metadata だけを保持する。本の source copy、PDF、抽出 text は tracked
  せず、build、CI、review、再開の依存にしない。
- `.github/workflows/lean_action_ci.yml` の push branch を `main` から `rewrite-main` へ変更し、
  pull request でも同じ build/check を実行する。
- `README.md` / `DESIGN.md` の link は相対 link を優先し、legacy 証跡だけは anchor SHA の
  permalink を使う。`/blob/main/` を新系列の current link として残さない。

削除 scope は bootstrap PR 内で read-only inventory を取り、legacy anchor から常に回収
できることを確認する。bootstrap PR の最終 head は `lake build`、closed-tree、layer、
empty-blueprint、actual-axiom、全 declaration doc-comment、空 docs と fixture に対する public
math docs/TeX sync check をすべて通す。checker 自体は doc comment あり/なしの private/public
fixture と、正/負の claim-reference fixture に加え、valid current prerequisite、early consequence、
future-target/cyclic prerequisite、completed-history prerequisite の fixture で fail/pass を検証する。
途中の壊れた commit を trunk に置かず、
atomic PR 全体だけを merge する。

旧 API への compatibility shim、deprecated alias、facade は作らない。旧 proof を参照する時は
`git show 01bcb49d49db92c225cfa74b74d409dd0a9c4edc:<path>` 等で読み、新 source から
import せず、code を copy せず、commit/file を cherry-pick しない。

### R2: complete source census and freeze

- Chapter 2--11、Appendix A、Solutions pp. 493--520 と全 out-of-scope page を inventory する。
- machine candidates をすべて closed disposition の atomic source claim に結び、番号付き数式、
  unnumbered obligation、独立 assertion を別 claim ID にし、definition/notation/hypothesis/domain/
  conjecture/out-of-scope と zero-item page も記録する。
- printed/PDF page の二 locator と problem/solution link を検査する。
- human first pass と fresh independent second pass を完了する。
- unresolved candidate、unclassified equation/obligation/independent conclusion、unreviewed page、
  duplicate active claim ID、non-claim member を持つ slice、disposition/lifecycle mismatch、derived
  assertion の role/edge 未分類・重複をゼロにする。
- source index を hash-lock し、source/derived claim ID と ordered slice ID の別 schema、
  append-only/tombstone policy、disposition-aware base-diff/source-assertion-frontier checker を有効にする。

R2 が完了するまで数学定義・statement・proof の実装 PR を開始しない。census は chapter ごとの
reviewable PR に分割してよいが、最後の freeze gate が通るまでは全て inventory work である。

### R3: first realization slice

- exact slice は `TASAKI2020-SLICE-C02-S01-001` とし、下記 backlog group 1 の先頭に列挙する
  atomic claim ID だけを source order の順序付き member とする。最初の statement frontier は
  self-adjoint assertion、次は eq. (2.1.1) assertion であり、proof frontier はまだ進めない。
- `SPIN-OPERATOR` definition と `AXIS-NOTATION` notation を current assertion の非 frontier
  dependency として scratch 実装し、それぞれ `declaration-bound` / `notation-implemented`
  binding を作る。definition の required-law list は `SELFADJOINT-COMPONENTS` と `EQ-2.1.1` を
  指す。Levi-Civita notation は Appendix A.3.1 claim への `required_by` dependency とする。
- `SELFADJOINT-COMPONENTS` と `EQ-2.1.1` assertion にだけ built `...Statement : Prop`、statement
  digest、non-vacuity obligation を置いて `typed` とする。definition/notation に架空の
  `Statement` / proof binding を置かない。
- source order 上で後に現れる Casimir、`S = 1/2, 1, 3/2, ...` domain assertion、Hilbert
  dimension を R3 に先取りしない。kernel の `N=0` は `consequence` derived assertion なので
  source domain proof-terminal 前には eligible でなく、この slice に入れない。
- 各 atomic claim の source locator と stable claim ID を対応する doc comment に置く。
- source equivalence、hypothesis strength、quantifier order、row/column semantics、non-vacuity を
  assertion ごとに独立 review し、definition/notation は展開先と consumer binding を review する。
- public/private 全 declaration の doc-comment gate と、対応する公開 math docs/TeX の locator/
  claim-ID 同期を R1 の generic checkerで通す。
- bootstrap infrastructure の追加・修理、many-body、graph、future chapter の準備を混ぜない。

この段階では many-body、graph Hamiltonian、infinite-volume framework を作らない。

### R4: first proof slice

- R3 で assertion ごとに凍結した statement digest を変えず、source order に対応 proof theorem を
  **proof-eligible assertion にだけ**追加する。definition/notation を proof 対象にしない。後続
  assertion への遷移は checker が先行 assertion の同 phase 到達後として検査する。
- assertion/proof definitional equality、basis-column action/endpoint semantic test、non-vacuity、
  actual axiom exact-set、全 declaration doc-comment gate、全 module build を通す。
- proof に derived assertion が不可欠なら、`prerequisite` role と current proof frontier assertion
  への `required_by` を登録し、target に依存しない DAG 順で先に完成させる。`consequence` や
  future source claim 由来の結果を prerequisite として利用しない。
- project axiom set が空なら assertion ごとに `proved`、非空なら `proved-relative` を生成する。
  両 required law が proof-terminal になれば `SPIN-OPERATOR` は自動で
  `definition-implemented-with-laws` へ進み、notation status は R3 のまま保持する。slice status は
  member status からだけ集約する。

### R5 onward: front-to-back repetition

各 frontier source assertion（review 単位は ordered slice）について R3/R4 を繰り返す。
definition/notation/hypothesis/domain は current assertion の非 frontier dependency としてだけ
実現する。derived assertion は次の二経路だけを許す。`prerequisite` は現在の source proof
frontier assertion の backward chain に必要で、そこへの `required_by` と非巡回 dependency DAG
を持つ場合だけ先行できる。`consequence` は全 `derived_from` parent の required terminal 後に
だけ進める。いずれも source assertion frontier を進めない。

### R6: chapter audit

chapter milestone では旧 declaration 数でなく frozen source census を基準にする。対象 claim の
未分類、disposition required state 未到達、assertion の `catalogued` / `typed` 残存をゼロにし、
`proved-relative` / `approved-deferred` は axiom-free 完了と別集計する。content/disposition-specific
digest、actual axiom、non-vacuity、orphan、layer、source-assertion frontier history、derived role/edge
eligibility history と dependency DAG を全件再監査する。

## Initial Tasaki front-to-back backlog

R2 の全巻 census freeze 後の最初の execution frontier は、「既存コードで完成度が高い順」では
なく、Tasaki 1st ed., Springer 2020, §2.1, pp. 13--20 の印刷順である。次の10項目は backlog
**group** であり、source claim ID ではない。各 group は番号付き数式、unnumbered obligation、
独立結論ごとの atomic claim と、それらを並べた implementation slice に展開する。group や
slice を一個の statement/status として扱わない。これらは全巻 source index の先頭部分であり、
ここだけを先に catalogue として完成扱いするものでもない。

1. **`tasaki-2020-2.1-single-spin-foundation`, §2.1, pp. 13--14**
   - exact first implementation slice は **`TASAKI2020-SLICE-C02-S01-001`**。その ordered
     members と exact lifecycle は次の通りである。
     1. `TASAKI2020-CLAIM-C02-S01-SPIN-OPERATOR`: `definition`。`Ŝ=(Ŝ⁽¹⁾,Ŝ⁽²⁾,Ŝ⁽³⁾)` の
        declaration binding を作り R3 で `declaration-bound`。下記二 assertion を required
        law とし、両者の R4 terminal 後に `definition-implemented-with-laws`。proof frontier ineligible。
     2. `TASAKI2020-CLAIM-C02-S01-AXIS-NOTATION`: `notation`。`1,2,3` axis notation と展開先を
        bind して `notation-implemented`。proof frontier ineligible。
     3. `TASAKI2020-CLAIM-C02-S01-SELFADJOINT-COMPONENTS`: `assertion`。R3 で `typed`、R4 で
        `proved` / `proved-relative`。最初の statement/proof frontier。
     4. `TASAKI2020-CLAIM-C02-S01-EQ-2.1.1`: `assertion`。R3 で `typed`、R4 で proof-terminal。
        二番目の statement/proof frontier。
     Levi-Civita symbol は Appendix A.3.1 の notation claim を `required_by` で実現する非 frontier
     dependency であり、slice member や独立 assertion を捏造しない。
   - 以後の slice と source assertion frontier は原典順に固定する。
     - **slice 002**: unnumbered Casimir assertion `Ŝ²=S(S+1)1̂`, p. 14。
     - **slice 003**: `TASAKI2020-CLAIM-C02-S01-SPIN-DOMAIN` assertion
       (`S=1/2,1,3/2,2,...`)。これが proof-terminal になった後だけ
       `LATTICE-DERIVED-SPIN-N-ZERO` `consequence` assertion を `typed → proved` にできる。
       source domain への `derived_from` を持ち、source coverage に数えず、source frontier の
       位置を持たず、次 frontier を進めない。
     - **slice 004**: `h₀` の `definition` record を非 frontier dependency として実現した後、
       `(2S+1)` dimensionality assertion を進める。
     - **slice 005/006**: basis/ladder notation を非 frontier dependency として実現し、
       **eq. (2.1.2)** / **eq. (2.1.3), p. 14** assertion を個別に進める。
   - これは抽出本文の順、spin operator definition → components self-adjoint → eq. (2.1.1) →
     unnumbered Casimir → `S` domain → Hilbert dimension → basis actions に一致する。R2 reviewer は
     printed page と照合してこの順序を freeze する。definition/notation/binder の必要依存は
     assertion frontier を占有しないが、後の source assertion を先に proof-terminal にしてよい
     という意味ではない。
   - concrete kernel は `N : ℕ`、basis index `k : Fin (N+1)`、**`m(k)=N/2-k`**、`k=0`
     highest、`k=N` lowest、row=output/column=input とする。ただしこの derived representation
     choice を Tasaki の先行 source claim と偽らない。
   - 定義実装の都合で proof の宣言順を逆転させず、public source-order section もこの順に
     する。matrix は row=output/column=input とし、ladder action と endpoint annihilation は
     column で検査する。site、graph、many-body、rotation は入れない。
2. **`tasaki-2020-2.1-spin-half-actions`, §2.1, p. 14**
   - spin-half notation と basis actions eqs. (2.1.4), (2.1.5)。backlog group 1 の specialization。
3. **`tasaki-2020-2.1-matrix-representations`, §2.1, pp. 14--15**
   - basis column eq. (2.1.6)、spin-half matrices eq. (2.1.7)、その直後の square/
     anticommutator、Pauli matrices eq. (2.1.8)、spin-one matrices eq. (2.1.9)。
4. **`tasaki-2020-problem-2.1.a`, §2.1, p. 15; solution p. 493**
   - 任意の `(2S+1) × (2S+1)` operator が `1̂,Ŝ¹,Ŝ²,Ŝ³` の polynomial であること。
5. **`tasaki-2020-2.1-rotation-definition`, §2.1, p. 15**
   - `Ûθ⁽ᵅ⁾ := exp[-iθŜ⁽ᵅ⁾]`、unitarity、same-axis group law、adjoint。eq. (2.1.10)
     より前の unnumbered claims。
6. **`tasaki-2020-2.1-rotation-matrices`, §2.1, pp. 15--16**
   - operator transformation eq. (2.1.10)、three-dimensional rotation matrices
     eq. (2.1.11)、entry formula eq. (2.1.12)。
7. **`tasaki-2020-2.1-rotation-conjugation`, §2.1, p. 16**
   - eqs. (2.1.13)--(2.1.16) と、本文の proof eqs. (2.1.17), (2.1.18)。
8. **`tasaki-2020-2.1-vector-covariance`, §2.1, p. 17**
   - `Ŝ·v` の covariance eqs. (2.1.19), (2.1.20)。
9. **`tasaki-2020-2.1-special-rotations`, §2.1, pp. 17--18**
   - `π` / `π/2` conjugation eqs. (2.1.21), (2.1.22)、`2π` rotation eq. (2.1.23)、
     π-rotation relations eqs. (2.1.24), (2.1.25)。
10. **`tasaki-2020-problem-2.1.b`, §2.1, p. 18; solution p. 493**
    - 先に本文の spin-half closed form eq. (2.1.26) を statement として登録し、直後の
      Problem 2.1.b の derivation で証明する。

以後も Problem 2.1.c, d, e、Z₂×Z₂ の定義と eq. (2.1.27) 以降、Problems 2.1.f, g の
印刷順を守り、§2.1 完了後にだけ §2.2 へ進む。§2.2 到達時に初めて `Volume`、generic
`Config/Ket/Op`、bosonic `embedSite` を導入し、total spin、global rotation、sector
decomposition を §2.2 の source order で追加する。§2.2 より前に future-proof な many-body
kernel を作らない。

Appendix の一般論は、本文の現在 atomic claim が必要とする時に mathlib と照合し、必要最小限を
`Math` に置く。Appendix 全体を先回りして形式化しない。旧 Theorem 2.4、Chapter 4、AKLT、
Hubbard の完成 proof を先に救出しない。

## Acceptance criteria

### This design PR

- 本ファイルだけが変更されている。
- 基準 SHA と各主要測定値に再測定 command がある。
- Adopt / Rewrite / Drop が file または pattern の根拠付きで分類されている。
- canonical representation、graph/volume boundary、generic local basis、coupling bundle が
  decision として記録されている。
- dependency DAG と初期 directory が一方向である。
- complete reset の closed keep allowlist、legacy TeX/docs/status 複製の不存在、新系列の
  public math docs/TeX の single-source/generation/reference rule が確定している。
- axiom の自動移植禁止、専用 path/namespace/taxonomy、defer 境界が明記されている。
- source/derived claim ID と ordered slice ID の分離、disposition-specific binding/digest/status/
  phase eligibility、source-assertion frontier、anti-regression policy が明記されている。
- derived assertion が `consequence` / `prerequisite` に排他分類され、parent-terminal と
  current-frontier/acyclic-DAG の eligibility が区別されている。
- assertion だけが Statement/proof lifecycle を持ち、definition/notation、hypothesis/domain、
  conjecture/out-of-scope がそれぞれ declaration/law、binder、nonproof terminal を持つ。
- §2.1 の source domain `S=1/2,1,...`、derived `N=0`、`m(k)=N/2-k`、matrix row/column convention、
  legacy endpoint lemma の negative evidence と drop 判定が明記されている。
- bootstrap が設計承認後の別 PR であり、本 PR が現コードを変更しないことが明記されている。
- compatibility shim を作らないことが明記されている。
- initial backlog が §2.1 から始まり、many-body kernel を §2.2 より前に作り過ぎない。
- coverage、first slice、spectral、volume、coupling、fermion を含む P0 decision がすべて
  本文と末尾の decision register で確定し、未決 P0 がゼロである。
- この PR の変更が本設計文書一つだけである。

### Bootstrap PR

- 旧 `main` が変更されず、legacy tip が参照可能である。
- 削除対象の read-only inventory と回収方法が記録されている。
- 旧 `LatticeSystem/**`、tests、root aggregator、status、scripts/checkers/workflows、legacy TeX、
  site/history/catalogue/docs が final tree に存在しない。
- 既存 code の carry-forward/import/copy/cherry-pick がなく、path 再利用も scratch rewrite である。
- 内容を保持した file が `lean-toolchain` と `lake-manifest.json` だけで、closed-tree check が通る。
- 承認済み設計が root `DESIGN.md` にあり、legacy docs/TeX は存在しない。新系列の manifest 登録
  public math docs/TeX は許容され、手編集 status 正本にはならない。
- package/toolchain は再現可能で、依存更新を混ぜていない。
- minimal `lake build` が warning zero で通る。
- closed-tree、disposition-aware atomic-claim/ordered-slice blueprint schema、layer、forbidden proof
  construct、actual axiom、source-assertion-frontier monotonicity check がある。
- derived assertion role/edge 排他、consequence parent terminal、prerequisite target=current proof
  frontier（初回遷移時）、immutable eligibility history、dependency DAG 非巡回を検査する
  schema/checker fixture がある。
- public/private を含む全 project declaration を検査する `docBlame` / `docBlameThm` / `#lint`
  相当の専用 doc-comment gate があり、fixture と CI が通る。`mathlibStandardSet` と
  `warningAsError` だけを合格根拠にしない。
- 空 docs と正/負 fixture で動く generic public math docs/TeX checker が R1 にあり、claim ID、
  locator、書誌、binding digest、generated status region の同期を CI で検査する。
- public root が DAG tip aggregator ではない。
- CI の push target が `rewrite-main` で、required check が branch protection に登録される。
- direct/force push が禁止され、current link に `/blob/main/` が残らない。
- bootstrap final head の全 check が成功し、壊れた中間 commit を trunk に置いていない。

### Complete census freeze

- Chapter 2--11、Appendix A、Solutions pp. 493--520 の全対象が inventory されている。
- Chapter 1、front matter、references、index 等も `out_of_scope` page として記録されている。
- named item、全番号付き数式、unnumbered proof obligation、独立結論、zero-item page を二巡監査した。
- printed/PDF page 二 locator、problem/solution link、disposition が全件にある。
- machine candidate 未解決、未分類 atomic claim、未監査 page、duplicate active claim ID、
  source claim ID と slice ID の混同、disposition/lifecycle mismatch、derived assertion の
  role/edge 未分類・重複がゼロ。
- source index が hash-lock され、source/derived claim stable ID が append-only、slice が claim ID
  の順序付き集約である。
- この acceptance 前に数学実装 PR が一つも始まっていない。

### Each realization PR

- 全 record が atomic claim stable ID、edition、section、printed/PDF page、number/subclaim key を
  registry に持ち、Lean-bound disposition の declaration だけが同 locator を doc comment に持つ。
  Lean binding 禁止の `out_of_scope` に架空の doc comment/declaration を要求しない。
- manifest が全 claim に `content_digest`、disposition、status、phase eligibility を持ち、assertion
  だけに statement digest/non-vacuity、definition/notation に declaration/law binding、
  hypothesis/domain に binder binding、conjecture/out-of-scope に nonproof terminal を要求する。
- assertion result theorem を含まず、独立 source-equivalence review に合格する。
- source-assertion statement frontier、明示 Appendix dependency、または role-valid derived
  assertion であり、slice は contiguous ordered aggregate にすぎない。非 assertion は current
  consumer の dependency に限る。
  derived assertion は consequence parent-terminal または prerequisite target=遷移時 base current
  proof frontier のどちらか一方の eligibility を満たす。
- assertion は本文より強い仮定がなく、quantifier order と consistency/non-vacuity evidence が
  ある。他 disposition は上表の required state に到達する。
- public/private を含む全 declaration の doc-comment gate と、公開 docs/TeX の claim-ID/locator/
  digest 同期 check に合格する。

### First implementation slice

- slice ID は `TASAKI2020-SLICE-C02-S01-001` で、R2 で freeze した ordered member claim 以外を
  含まない。各 member が固有 binding/status/digest/frontier eligibility を持ち、slice 全体の
  `ItemStatement` や手編集 status は存在しない。
- ordered member は `SPIN-OPERATOR` definition → `AXIS-NOTATION` notation →
  `SELFADJOINT-COMPONENTS` assertion → `EQ-2.1.1` assertion。前二者は R3 で declaration binding
  を得て、spin definition は後二者の R4 terminal 後に `definition-implemented-with-laws` となる。
  後二者だけが R3 `typed` / R4 proof-terminal になる。
- 次の source assertion は slice 002 Casimir、slice 003 `S=1/2,1,...` domain、slice 004 dimension。
  `N=0` は `consequence` derived assertion であり、domain proof-terminal 後だけ eligible で、
  source frontier を進めない。
- `m(k)=N/2-k`、`k=0` highest、`k=N` lowest、row=output/column=input は derived concrete
  representation choice として doc comment、semantic test、公開数学 docs/TeX に記録する。
- legacy endpoint row lemma の名称・物理解釈を移植せず、`S⁺` highest / `S⁻` lowest annihilation
  は basis-vector column action として検査する。
- R3 は disposition-specific realization、R4 は assertion の凍結 statement に対する proof だけを
  source order で進め、many-body、graph、rotation、future helper を含めない。

### Each proof PR

- proof-eligible assertion のみを対象にし、凍結済み statement digest を変えていない。
- proof type が対応 assertion と definitionally equal である。
- derived prerequisite を含む場合、`required_by` target が遷移時の current source proof frontier、
  dependency DAG が非巡回で、prerequisite 側から target declaration/proof への依存がない。
  consequence を先行利用していない。
- final line から必要性を説明できない declaration がない。
- 全 module build warning zero、禁止 proof construct zero、actual axiom exact-set 合格。
- unrelated atomic claim、future helper、compatibility work を含まない。
- orphan declaration がなく、status が environment から正しく生成される。
- public/private を含む全 declaration の doc-comment gate と、必要な公開 docs/TeX 同期に合格する。
- independent verification review に合格する。

### Chapter 2 milestone

- §2.1--§2.5 の atomic source claim が印刷順に追跡可能である。
- spin-half と general-spin の many-body kernel が一つである。
- graph の有限性と finite volume の有限性が分離されている。
- public theorem が proof-route helper や `Matrix.toLin'` を露出しない。
- 旧 source を import せず、旧実装と同等の対象 statement を新 axiom policy 下で再現する。
- Chapter 2 census の未分類、disposition required state 未到達、assertion の `catalogued` / `typed`
  がゼロである。
- derived assertion の role/edge mismatch、未完 prerequisite、parent 前 consequence がゼロである。
- `proved-relative` / `approved-deferred` が axiom-free `proved` と別集計される。

## P0 decision register

以下をすべて **decided** とする。未決 P0 はゼロである。

1. **trunk**: 新 trunk は `rewrite-main`。bootstrap merge 後に repository default を
   `rewrite-main` とし、build/layer/status/axiom/doc-comment/public-doc-sync checks を required にする。旧 `main` は
   anchor `01bcb49d49db92c225cfa74b74d409dd0a9c4edc` を含む frozen legacy として保護する。
2. **package / namespace**: package name と root namespace `LatticeSystem` は維持する。
   旧 declaration/import path の互換性は維持しない。
3. **complete reset allowlist**: 旧内容を保持するのは `lean-toolchain` と
   `lake-manifest.json` のみ。旧 code/tests/status/scripts/workflows/legacy TeX/docs は全面削除し、
   再利用 path も scratch rewrite。承認済み設計は root `DESIGN.md` に移す。新系列の manifest
   登録 public math docs/TeX は後続追加を許容する。
4. **blueprint / generated status**: source/derived atomic claim ID と implementation slice ID を
   分離する。番号付き数式、unnumbered obligation、独立結論ごとに source-order key、二 locator、
   disposition、`content_digest`、disposition-specific binding/digest/status/phase eligibility を持つ。
   assertion だけが statement/proof/axiom binding を持ち、definition/notation は declaration/law、
   hypothesis/domain は binder、conjecture/out-of-scope は nonproof terminal を持つ。slice は claim ID
   の順序付き list だけを持ち、独自 statement/status 正本にしない。source-assertion frontier と
   status は claim registry と Lean environment から生成する。derived assertion は
   `consequence` (`derived_from`) / `prerequisite` (`required_by`) の排他的 role を必須とする。
5. **logical axiom baseline**: proved capstone の project-specific axiom は既定で空集合。
   Lean/mathlib の logical axioms `propext`、`Classical.choice`、`Quot.sound` は許容 universe
   とし、各 capstone record には実際に使う subset を完全一致で記録する。それ以外は
   current closed taxonomy 内の explicit approved-deferred record がなければ reject する。
6. **file / compile budget**: 700 行を responsibility review trigger、900 行を強い split
   signal とするが、数値だけで機械分割しない。compile/import budget は最初の Chapter 2
   実測を baseline とし、各 PR で delta を記録する。
7. **coverage census**: 数学実装前に Chapter 2--11、Appendix A、Solutions pp. 493--520 の
   named items、全番号付き数式、unnumbered obligations、独立結論を atomic claim として二巡監査し hash-lock する。
   Chapter 1/front matter/references/index も `out_of_scope` page として記録する。
8. **first implementation slice**: `TASAKI2020-SLICE-C02-S01-001`, 1st ed. §2.1,
   pp. 13--14。member は spin-operator definition → axis notation → self-adjoint assertion →
   eq. (2.1.1) assertion。続いて slice 002 Casimir → slice 003 `S=1/2,1,...` domain assertion →
   slice 004 dimension assertion → eqs. (2.1.2), (2.1.3) を原典順に進める。`N=0` derived assertion
   は `consequence` であり、domain proof-terminal 後だけ eligible で source frontier を進めない。
9. **spectral API**: `Matrix` が計算 canonical、Hermitian proof を持つ `Observable` が
   self-adjoint な物理量の API。`IsEigenvector` は nonzero を含み、spectral bridge は
   `Quantum.Finite.Spectrum` だけに置く。
10. **volume API**: configuration restriction、graph/coupling restriction、operator identity
    extension、equivalence reindexing と、それぞれの identity/composition/naturality law を
    初期 many-body API の完了条件とする。canonical でない ket extension は置かない。
11. **weighted support**: `zero_of_not_adj` を base semantics とし、非零 weight edge を
    `activeGraph` とする。connectivity、bipartition、ferro/antiferro sign は activeGraph 上の
    refinement bundle に置く。
12. **fermion representation**: carrier/volume/reindexing だけを共有し、bosonic `embedSite`
    を fermion API に使わない。Chapter 9 で ordered Jordan--Wigner を canonical とし、
    graded/CAR 一般化は実需要まで行わない。
13. **bootstrap atomicity / CI / citations**: R1 の最終 tree で build/root/closed-tree/layer/
    blueprint/axiom/monotonicity checks、および private を含む全 declaration の
    `docBlame` / `docBlameThm` / `#lint` 相当 gate、空 docs と正/負 fixture で動く generic public
    math docs/TeX sync checker、`rewrite-main` CI を同時成立させる。書誌・hash metadata のみ
    tracked し、本の source copy を置かない。
14. **disposition lifecycle**: assertion だけを `catalogued → typed → proved/proved-relative/
    approved-deferred` とし realization PR と proof PR を分ける。definition/notation は declaration
    と必要 law、hypothesis/domain は binder binding、conjecture/out-of-scope は nonproof terminal。
    derived consequence は parent terminal 後、derived prerequisite は遷移時 base current source
    proof frontier への required-by、immutable eligibility history、非巡回 DAG の下だけで先行可。
    `sorry` stub/temporary axiom は使わず、
    stable claim ID は append-only+tombstone/supersession とする。
15. **axiom isolation**: `LatticeSystem/Axioms/**` は空から始め、閉じた taxonomy、path/namespace、
    directional import、exact registry/environment gate を強制する。`proved` は project axiom
    zero、依存 result は `proved-relative`、axiom は `approved-deferred`。列挙外の解析的対象は
    独立 design PR で新 category/path が承認されるまで axiom 化しない。
16. **anti-regression / protection**: source deletion、disposition-specific status downgrade、
    content/binding/locator drift、axiom expansion、binding 消失、source-assertion frontier violation
    と、仮定強化・結論弱化・量化域縮小等の semantic regression を base-diff gate で reject する。
    derived role/edge flip、consequence の早期進行、non-current/cyclic prerequisite も reject する。
    全 digest change は disposition に対応する dedicated change PR と独立 review を要求する。
    foundation change は impact closure 付き dedicated PR。`rewrite-main` は direct/force push 禁止、
    independent realization/verification review 必須とする。
17. **source fidelity / basis semantics**: Tasaki の source assertion `S=1/2,1,...` と kernel の
    `consequence` derived assertion `N=0` を分離する。basis は `m(k)=N/2-k`、row=output、column=input。legacy
    `SpinS/Operators.lean` の係数・基底順だけを再照合候補とし、endpoint row lemma の誤名・
    物理解釈は negative evidence として drop する。
18. **public math docs/TeX**: legacy status/catalogue/TeX 複製は drop するが、新系列の公開数学
    docs/TeX は禁止しない。書誌/locator は references+claim registry、typed assertion statement
    と definition/notation declaration は Lean、status/frontier は environment-derived data を
    正本とし、docs/TeX は claim ID を参照して
    文献名・定理/式番号・printed/PDF page を明記し、数学変更 PR と同時同期する。

## Documentation sync conclusion for this PR

本 PR は review 中の再設計提案一ファイルだけを変更し、現在の実装・公開 status を変更しない。
したがって本 PR では README や旧公開物を同期しない。設計承認後の R1 で legacy `tex/` と旧
docs/status 複製を全面削除し、本設計を root `DESIGN.md` へ移し、README と current branch link
を scratch rewrite する。以後の status は claim registry/binding と Lean environment からだけ
生成する一方、新系列の公開数学 docs/TeX は claim ID を参照する従属文書として数学変更 PR と
同時に追加・同期できる。
