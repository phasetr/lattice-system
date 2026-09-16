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
   path を再利用する場合も内容は scratch rewrite とする。byte-preserve する実装系 file は
   `lean-toolchain` と `lake-manifest.json` だけとし、`AGENTS.md`、`CLAUDE.local.md`、`LICENSE`、
   git metadata 等の project governance/legal metadata は保持して新系列の phase override へ改訂する。
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
    `ItemStatement` や status 正本にしない。exact theorem skeleton→proof lifecycle は assertion
    disposition だけに適用する。definition/notation は declaration と必要 law、hypothesis/domain
    は consumer の binder/metadata、conjecture/out-of-scope は非 proof terminal として別 lifecycle
    を持つ。derived assertion は parent terminal と source-order passage 後の `consequence` と current proof frontier に
    必要な `prerequisite` を排他分類する。全 assertion は skeleton phase に exact theorem
    statement `:= by sorry` として一度だけ型検査する。未解決 assertion registry entry、theorem
    declaration/module、その declaration value にある direct `sorryAx` occurrence を一対一にする。
    stub module は production root/import graph から隔離する。proof phase では theorem name、exact
    type、statement digest、module path を固定し、proof body を置換する。import 追加は既 proved かつ
    transitive `sorryAx`-free の先行/prerequisite module だけに限る。未登録 `sorry`、`admit`、
    `native_decide`、temporary axiom は禁止する。
15. project axiom は空の `LatticeSystem/Axioms/**` から始め、専用 path/namespace、閉じた分類、
    exact environment check の下でのみ追加できる。project axiom が空の result だけを
    `proved`、依存する result を `proved-relative`、axiom 自身を `approved-deferred` とする。
16. Tasaki §2.1 の `S=1/2,1,...` は source `domain` claim のまま保持し、`N : ℕ` kernel の `N=0` は
    別 `consequence` derived assertion とする。basis は `m(k)=N/2-k`、matrix は
    row=output/column=input とする。
17. legacy status/docs/TeX は全面削除し、reset 後の `docs/` / `tex/` は存在させない。必要最小の
    人間向け文書は root `DESIGN.md` / `README.md`、machine-readable data は `blueprint/` /
    `references/` に限定する。新しい docs/TeX はユーザーの将来の明示承認なしに作らない。
18. warning-as-error/standard linter とは別に、private を含む全 project declaration の doc
    comment を `docBlame` / `docBlameThm` / `#lint` 相当で CI gate する。
19. 工程は **全巻 two-pass census/hash lock → source vocabulary/type layer の scratch 実装 →
    全巻 typed assertion skeleton の build/freeze → front-to-back proof discharge** の四段階に固定する。
    skeleton freeze acceptance 前に proof PR を開始しない。

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
- theorem/proof、source locator、prospective approved project-axiom set、proof 後の actual axiom set、
  status の関係を一意にする。
- 全巻 atomic source claim を実装前に列挙し、未実装が不可視になる余地をなくす。
- 小さい import surface と一方向の dependency DAG を保つ。
- production build は warning zero、`sorryAx` / `admit` / `native_decide` 不在を継続する。
  skeleton build では registry-bound stub の `sorry` warning だけを局所許容し、他 warning は error とする。
- 強い仮定を置く theorem について、仮定の同時充足可能性と結論の非空虚性を確認する。
- 無限体積極限を長期目標として保持しつつ、Chapter 2 より先に C\*-algebra framework を
  作り込まない。

## Non-goals

- 旧 namespace、declaration name、import path の互換維持。
- 旧 source/test/checker/status catalogue/site/history/TeX の複製を「ひとまず」残すこと。
- 旧 source を新しい directory へ機械的に移動すること。
- 旧 catalogue の全行を新 status ledger へ機械的に移すこと。
- 旧 proof-stage module を順番に「きれいにする」漸進 refactor。
- 未登録 `sorry`、production-importable な sorry-backed theorem、temporary axiom を backlog 表現に
  使うこと。全巻 skeleton の登録済み・隔離済み stub はこの禁止の対象外である。
- legacy status を複製した TeX proof guide、またはユーザーの将来の明示承認なしに新しい
  `docs/` / `tex/` を作ること。
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

低層資産は file 単位で採用しない。採用単位は「失敗から得た設計判断」「再照合すべき数学的
アイデア」または「検証方法」であり、実装入力は Tasaki 原典と mathlib に限る。旧 code を
copy/import/API dependency にせず、commit や file を cherry-pick しない。各 implementation-slice PR は adopt gate の各項目について
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
- `docs/**` の全内容と、site/history/catalogue/limitations/roadmap、手編集 status を複製する
  site generator。reset 後は `docs/` 自体を置かない。
- `tex/**` の全内容と TeX workflow/reference。reset 後は `tex/` 自体を置かず、新しい TeX も
  ユーザーが将来明示的に承認するまで作らない。
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
    Vocabulary/                  # R3 の source vocabulary/type layer
      ...
    Claims/
      Chapter02/
        C02S01SelfAdjointComponents.lean  # atomic assertion 一件/細粒度 module
        C02S01Equation2_1_1.lean
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
```

`LatticeSystem.lean` は production-eligible な stable public surface だけを import する。R4 skeleton
target は manifest 上の全 claim module、production target は `sorryAx`-free の proved module だけを
import する。proof body 置換後は theorem name、module path、exact type、statement digest を保った
module を manifest 上で skeleton から proved に昇格させる。R4 stub は statement typing に必要な
shared vocabulary だけを import し、prospective axiom dependency を作るための unused `Axioms`
import や人工参照を置かない。R5 の proof PR が新たに追加できる ordinary claim-module import は、
既 proved かつ transitive `sorryAx`-free の source-order 上の先行 module、
または current frontier に承認済み `required_by` を持つ proved prerequisite module だけを import に
追加できる。これとは別に、**current prospective approved set**、すなわち R4 で freeze 済み、
または freeze 後の専用 axiom-policy/statement-dependency PR で source/rationale/user approval/
independent review/digest update 済みの集合に列挙された exact `Axioms` module は R5 で追加できる。
future/unproved/sorry-backed ordinary module と未登録
`Axioms` module は import できない。atomic assertion stub は相互に証拠依存しない細粒度 module
一件ずつとする。
本の本文、PDF、抽出 text、statement の大量引用は tracked しない。tracked に置くのは書誌、
locator、hash、formalization に必要な数学的 restatement だけである。

### Single source of truth and minimal tracked artifacts

旧 `docs/formalization/legacy/`、旧 status site、`tex/proof-guide.tex` のように同じ claim/status を
複数箇所へ手入力する構成は廃止する。complete reset 後の説明文書は root `README.md` と
`DESIGN.md`、machine-readable blueprint、書誌 reference だけに閉じる。`docs/` と `tex/` は
存在させず、新規 docs/TeX、その生成物、workflow、dependency はユーザーの将来の明示承認と
専用 design change があるまで追加しない。R1 で `CLAUDE.local.md` にこの rewrite-main phase
override を記録し、通常の公開 docs/TeX 同期規律より優先させる。

重複を避ける正本と生成/参照関係は次に固定する。

- 書誌、edition、page mapping、source fingerprint の正本は `references/tasaki-2020.json`。
- source locator、atomic restatement、source-order、claim/slice membership の正本は claim registry
  (`blueprint/tasaki-2020/source-index.json` と binding shard)。
- assertion が `skeletonized-unproved` になった後の形式 statement の正本は claim ID に bind された
  唯一の Lean theorem declaration、prospective approved project-axiom set/digest の正本は binding
  registry、proof 後の actual dependency の正本は Lean environment である。
  definition/notation の正本は bind された Lean declaration、hypothesis/domain の正本は bind
  された consumer binder、conjecture/out-of-scope の正本は disposition-specific registry record
  であり、存在しない `Statement` / proof binding を要求しない。
- atomic status、frontier、slice/chapter 集計は上記 registry/binding/environment から生成し、
  root 文書へ手編集 status table を複製しない。
- 全 atomic assertion の Lean doc comment が人間向け source trace の正本であり、claim ID、書名、
  edition、section、printed page、PDF page、theorem/equation/problem number、subclaim locator を
  省略なく持つ。definition/notation 等の Lean-bound record も対応 locator と claim ID を持つ。
- closed-tree checker は `docs/` / `tex/` と未承認の説明 artifact を reject する。将来承認される
  場合は、その PR で正本との生成/参照関係と checker を再設計する。

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

1. `admit`、`native_decide`、未登録 `sorry`、production import closure の `sorryAx`、temporary axiom
   を禁止する。唯一の例外は whole-book skeleton phase で registry と一対一に対応する
   `theorem ... := by sorry` であり、専用 skeleton module/build target に隔離する。
2. 旧 project axiom declaration 70 個は一つも自動移植しない。bootstrap 後の
   `LatticeSystem/Axioms/` は空から始める。
3. primitive vocabulary は axiom ではなく `structure` / `def` で表す。内容のない predicate
   も、命題を真とする証拠を与えない限り `def ... : Prop` とする。
4. axiom の許可 taxonomy は `CLAUDE.local.md` の defer 分類に対応するものだけとし、
   `OperatorAlgebra/{CStar,State,GNS,KMS}`、
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
    assertion binding は R4 freeze 時に、使用を将来許可する axiom ID/module の
    **prospective approved project-axiom set**、source/rationale、user approval、independent review、
    set digest を metadata として固定する。これは stub の actual dependency を主張しない。
    以後の **current prospective approved set** は、この R4 freeze 済み集合、または freeze 後の
    専用 axiom-policy/statement-dependency PR で source/rationale/user approval/independent review/
    digest update 済みの集合、と定義する。
11. CI は Lean environment の全 project axiom と registry を双方向完全一致で検査し、binding
    された **proof-terminal assertion declaration に限って** current prospective approved project-axiom set と
    actual project-axiom dependency set の完全一致を検査する。skeleton declaration は direct
    `sorryAx` exactly 1 を要求する一方、prospective set との actual 一致を要求せず、set を満たす
    ための unused import/人工参照を reject する。path/namespace 違反、未登録 axiom、存在しない登録、
    terminal proof の axiom set 過不足を reject する。`sorryAx` は共通 constant なので actual axiom
    set の要素を claim ごとに対応付けない。skeleton target では actual axiom set に `sorryAx` が
    含まれるかを検査し、個別対応は registry binding、declaration/module、後述の direct-body
    occurrence mapping で検査する。production target と `proved` / `proved-relative` result は
    direct/transitive のいずれの `sorryAx` も一つでも検出したら reject する。
12. proof-terminal result の project axiom dependency が current prospective approved set と一致して空なら
    `proved`、一致して非空なら
    `proved-relative`、axiom declaration 自身を `approved-deferred` と生成表示する。
    `proved-relative` を chapter の axiom-free 完了数へ算入しない。
13. ordinary assertion stub を axiom に置換して proof obligation を逃がしてはならない。意図的
    axiom は専用 stable axiom ID、許可 category、source locator、rationale、approval を持つ
    `LatticeSystem/Axioms/**` の別 declaration とし、actual declaration↔registry と proof-terminal
    consumer の actual dependency↔current prospective approved set を双方向に照合する。
14. freeze 後の新 axiom または prospective approved set の追加・拡大を通常 proof PR に混ぜない。
    必要なら専用 axiom-policy/statement-dependency change PR とし、source locator、数学的 rationale、
    user approval、independent review を得て registry/set digest を更新し、更新後の集合を current
    prospective approved set とする。sorry 数の増加、
    proved→stub、source frontier の迂回はこの例外でも禁止する。
15. 大型 theorem は細粒度の独立 assertion stub と supporting lemma に分割する。未証明 stub は
    skeleton tree にだけ置き、production root/import closure へ露出させない。

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
| `assertion` | exact type を持つ唯一の Lean theorem、`statement_digest`、不変 module path、prospective approved project-axiom set+digest、terminal proof の actual set、direct-body `sorryAx` count、non-vacuity obligation | `inventoried → catalogued → skeletonized-unproved (direct sorryAx = 1; actual-match not required) → proved` または `proved-relative` (direct/transitive sorryAx = 0; current prospective approved=actual)。承認 defer は通常 stub の変形でなく別 axiom record | source assertion の proof discharge のみ eligible |
| `definition` | Lean `def` / `structure` / `abbrev` と `declaration_digest`、actual axiom set、必要 law の assertion claim ID list | `inventoried → catalogued → declaration-bound`。law が無ければ `definition-implemented`、必要 law が全て proof-terminal なら `definition-implemented-with-laws` | ineligible。consumer assertion の非 frontier dependency |
| `notation` | notation/syntax declaration、展開先、`declaration_digest`、展開先 declaration の actual axiom set、必要 law claim ID list | `inventoried → catalogued → declaration-bound → notation-implemented`。law があれば全 law terminal を要求 | ineligible。consumer assertion の非 frontier dependency |
| `hypothesis` / `domain` | consumer claim ID、binder 名・型・量化位置の `binder_digest` | `inventoried → catalogued → binder-bound` | ineligible。consumer assertion の非 frontier dependency |
| `conjecture` | normalized statement の `content_digest`。型検査が必要なら証拠を与えない `def ... : Prop` だけを任意 binding | `inventoried → catalogued → conjecture-recorded` | permanently ineligible。proof/axiom binding 禁止 |
| `out_of_scope` | page/range、理由、`metadata_digest` | `inventoried → out-of-scope-recorded` | permanently ineligible。Lean binding 禁止 |

definition/notation の law は同じ record 内の手書き checkbox で済ませず、独立した source/derived
`assertion` claim ID として通常の statement/proof lifecycle を通す。hypothesis/domain record は
真であることを証明する claim ではなく、どの consumer のどの binder が原典の仮定・量化域を
表すかを検査する。外部文献に証明を委ねる assertion も消さず、新 axiom policy に従って
prove/defer を判断する。definition の well-definedness、closure、independence-of-choice 等、証明を
要する性質は definition record に埋めず、別の atomic assertion stub とする。

初期 blueprint は metadata と数学的 restatement を持つ。R3 で全巻の assertion を型として表現
できる source vocabulary/type layer を scratch 実装し、R4 で全 source assertion を一括して
skeletonize する。したがって statement visibility は全巻 freeze され、順序制約を受けるのは
R5 以後の **proof discharge frontier** である。frontier は slice でなく proof-eligible source
assertion ID だけから最古の未 proof-terminal assertionとして計算する。definition/notation/
hypothesis/domain は R3 の非 frontier dependency、conjecture/out-of-scope は disposition-specific
terminal であり、proof frontier を占有しない。derived assertion の skeletonization と proof
eligibility は分離し、dependency role ごとに次を課す。

- **`consequence`**: 一つ以上の `derived_from` parent が全て disposition-specific required terminal
  に到達し、かつ source-order gate が全 parent の位置を通過した後だけ proof discharge eligible。
  assertion parent では proof-terminal、domain/hypothesis 等の非 assertion parent では R3 の binding
  terminal と R5 の source-order passage の双方を要求する。statement stub は R4 で型検査してよいが、
  parent より前に証明したり source proof の前提にしたりできない。
- **`prerequisite`**: `required_by` target がその時点の current **source proof frontier assertion**
  と一致し、その target が `skeletonized-unproved`、かつ target の final line から backward-chain
  した証明上の必要性が review 済みの場合だけ先行して proof discharge eligible。stub 自体は
  R4 で型検査してよい。全 prerequisite は target を
  root とする非巡回 DAG をなし、target またはその proof に依存してはならない。future/past source
  claim、単なる便利 helper、statement 構築だけを理由とする先行は reject する。

どちらも source assertion frontier の位置を持たず、完了しても frontier を進めない。一つの
derived assertion に両 role/edge を許さず、checker は role/edge cardinality、target=current
frontier、parent terminal/source-order passage、DAG acyclicity を environment dependency と registry
の双方から検査する。
ここで target=current は prerequisite の **最初の状態遷移時の base proof frontier** に対する
条件である。registry は target、base frontier key、承認済み dependency digest を immutable に
記録し、target 完了後は current でなくなっても履歴を再検証して completed prerequisite を保持する。

R3 で必要な型と語彙を実装した後、R4 の skeleton PR は atomic `assertion` claim ごとに次の
ような exact theorem declaration を build する。

```lean
/--
Hal Tasaki, Physics and Mathematics of Quantum Many-Body Systems,
1st ed., §2.4, Theorem 2.1, printed p. 35, PDF p. 52, subclaim (a).
Claim: `TASAKI2020-CLAIM-C02-S04-THM-2.1`.
-/
theorem theorem21_subclaim_a (/* exact binders */) : ExactStatement := by
  sorry
```

同じ theorem に三つの独立 assertion があれば三つの claim ID と三つの細粒度 stub を置き、
conjunction 一個で一括 binding しない。各 stub は独立 module に置き、whole-book skeleton target
だけが import する。production root と proved module は unresolved stub module を import できない。R5 の
proof PR は theorem name、declaration の exact type、`statement_digest`、module path を変えず、
同じ declaration の body を proof に置換する。必要な import は、既 proved かつ transitive
`sorryAx`-free の source-order predecessor、または current target の承認済み `required_by`
prerequisite module に限って追加できる。別枠で current prospective approved set、すなわち R4 で
freeze 済み、または freeze 後の専用 axiom-policy/statement-dependency PR で source/rationale/
user approval/independent review/digest update 済みの集合に列挙された `Axioms` module だけを追加できる。
assertion binding は **claim ID ごとに** declaration、module、statement
digest、prospective approved project-axiom set/digest、proof-terminal 時の actual set、non-vacuity
obligation を結ぶ。claim ごとの status と
transitive `sorryAx` は Lean environment から生成する。

skeleton target では manifest-bound stub の `declaration uses 'sorry'` warning だけを局所的に許す。
`warningAsError` を全面解除せず、その他の warning、`admit`、`native_decide`、未登録 `sorry` は
全 phase で error とする。ここで **direct `sorryAx` occurrence** は Lean environment の対象 theorem
`ConstantInfo.value?` expression を、参照先 declaration を unfold せず走査した時に現れる
`sorryAx` constant occurrence と定義する。各 `skeletonized-unproved` declaration は direct occurrence
を exactly 1 持ち、未解決 assertion registry entry ↔ theorem declaration ↔ module path ↔ direct-body
occurrence を exact bijection にする。source syntax の `:= by sorry` 一件と elaborated environment の
direct occurrence 一件を構文 checker と environment checker の双方で照合する。別 declaration への
依存を通じた transitive-only `sorryAx` は stub の正当化にならない。`proved` / `proved-relative`
entry とその declaration は direct/transitive occurrence とも zero とし、production eligibility も
transitive `sorryAx` が空の proved module に限る。

status field は人が書かない。claim registry、binding、Lean environment から上表の
disposition-specific status を atomic claim ごとに生成する。slice/chapter の status は atomic
status の順序付き集約から生成する。derived assertion の表示は status とともに role、eligibility
parent/target、frontier-history key を必ず示し、skeleton/proof status だけで先行可否を隠さない。tracked
prose を第二の status 正本にしない。

### PR unit and frontier

- R3 の vocabulary/type PR、R4 の whole-book assertion skeleton PR、R5 以後の assertion proof PR
  を分離し、binding/digest/status/phase eligibility は atomic claim ごとに独立させる。
- vocabulary/type PR は全巻 assertion の exact statement に必要な definition/notation declaration、
  hypothesis/domain binder metadata、conjecture/out-of-scope record を含むが、proof body を含まない。
- skeleton PR は全 atomic assertion の exact theorem stub と source equivalence/non-vacuity review を
  完成させる。R4 freeze acceptance 前は assertion proof PR を一件も開始しない。
- proof PR は assertion ごとの theorem name/module path/exact type/statement digest を変更せず、
  body と eligible import 増分、直前から backward-chain した必要補題、semantic test、environment
  verification を完結させる。追加 import は既 proved かつ transitive `sorryAx`-free の先行 claim
  または承認済み `required_by` prerequisite module だけとする。
- 大型 theorem だけ、同じ theorem issue の中で複数 PR に分割できる。各 PR はそれ自体で
  axiom-free な一つの数学結果を完成させ、最終 theorem のどの step に必要かを明記する。
- PR 分割の都合で `Core` / `Bridge` / `Final` file を増やさない。
- unrelated refactor、将来用 helper、別 chapter の準備を混ぜない。
- capstone 実装前に、本文との statement review と hypothesis audit を独立に行う。
- R4 で statement skeleton は全巻一括 freeze する。R5 以後は source-order 上の proof frontier を
  越えて proof-terminal へ遷移しない。同じ slice の後続 assertion も、先行 assertionが
  proof-terminal になった後でだけ discharge する。非 assertion member は R3 で必要 state を満たす。
  一つの atomic PR で contiguous な複数 member を進める場合、checker は base からの遷移を
  member 順に simulation し、gap/skip を reject する。現在の source proof frontier assertion の
  final line から必要な Appendix dependency と `prerequisite` derived assertion だけ、上記
  `required_by` / acyclic-DAG rule の下で先行できる。`consequence` は先行不可である。
- 旧 code を import または cherry-pick しない。proof idea を読む場合も、新 canonical API
  上で source から実装し直す。
- 各 slice PR に claim 別の `Legacy assessment` を置き、参照した旧 declaration ごとに
  `adopt idea / rewrite / drop`、adopt gate の判定、直接 code 移植がないことを記録する。

### Adopt gate for an old declaration idea

旧 declaration を数学的アイデアまたは negative evidence として参照するには、次をすべて満たす。

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
slice PR の claim 別 `Legacy assessment` に残し、設計 PR で旧資産全体を事前承認しない。この
gate を通っても旧 source の copy/cherry-pick/import を許可するものではない。

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
2. production build と whole-book skeleton build。production は warning zero、skeleton は registry-bound
   stub の sorry warning だけを許し、それ以外は warning zero。public root から未 import の対象も build する。
3. 専用 doc-comment gate。public/private を含む全 project declaration を environment から列挙し、
   `docBlame` / `docBlameThm` / `#lint` 相当で doc comment 欠落を error にする。
   `mathlibStandardSet` と `warningAsError` だけで代用しない。
4. `admit` / `native_decide` / 未登録 `sorry` 不在。skeleton では unresolved registry entry↔theorem
   declaration↔module path↔direct-body `sorryAx` occurrence の exact bijection、各 stub の direct count
   exactly 1、transitive-only dependency 不可を構文+environment で検査する。production と
   proof-terminal declaration は direct/transitive `sorryAx` とも不在。
5. skeleton assertion は prospective approved project-axiom set/digest の承認済み metadata と direct
   `sorryAx` exactly 1 を別々に検査し、project axiom の actual 一致や人工参照を要求しない。
   proof-terminal assertion だけ current prospective approved project-axiom set と actual dependency set の完全
   一致、direct/transitive `sorryAx` zero を要求する。definition/notation は実際の dependency を検査し、
   hypothesis/domain/conjecture/out-of-scope に存在しない proof axiom set を要求しない。
6. source locator、disposition-specific binding/digest/status/phase eligibility。全 assertion の Lean
   doc comment に claim ID、edition、section、printed/PDF page、theorem/equation/problem/subclaim
   locator が完全にあり、proof body 置換後も statement digest が不変であること。
7. dependency-layer 違反、import cycle、unregistered/orphan declaration がゼロ。proof PR の ordinary
   import 増分は既 proved かつ transitive `sorryAx`-free の source-order predecessor または承認済み
   `required_by` prerequisite だけとする。Axioms import 増分は current prospective approved set、
   すなわち R4 で freeze 済み、または freeze 後の専用 axiom-policy/statement-dependency PR で
   source/rationale/user approval/independent review/digest update 済みの集合の exact module だけとし、
   future/unproved/sorry-backed ordinary import と未登録 axiom import がゼロ。
8. semantic test と non-vacuity witness。強い hypothesis に witness がない例外は理由と独立承認を要求。
9. source index と base branch の diff に対する disposition-aware state/source-proof-frontier
   monotonicity check。derived assertion について consequence parent terminal/source-order passage、
   prerequisite target が
   その状態遷移時の base current proof frontier、role/edge 排他、dependency DAG 非巡回、完了後の
   immutable eligibility history も検査する。
10. closed-tree allowlist に合格し、`docs/` / `tex/`、未承認 artifact、legacy path、production から
    skeleton module への import が存在しないこと。
11. cold/warm のどちらかを明記した compile-time delta と import 増分の記録。

### Anti-regression gates

base branch と PR head の machine-readable diff で、次を default reject する。

- atomic claim の削除、stable claim ID の再利用、tombstone の復活、source claim ID と slice ID
  の混同、slice member の無承認並べ替え。
- disposition-specific terminal、`proved` / `proved-relative` / `skeletonized-unproved` からの無承認 downgrade。
  assertion の proof、definition/notation declaration、hypothesis/domain binder binding、terminal
  metadata record の消失。
- locator、disposition、`content_digest` または disposition-specific digest の silent change。
- semantic weakening、すなわち仮定の強化、結論の弱化、量化域の縮小、または同等の適用範囲・
  内容の後退。source 誤読訂正であっても旧 atomic claim を tombstone/supersession し、訂正根拠を
  dedicated statement-change PR で独立 review するまでは reject する。
- assertion statement change と proof change の同居。definition/notation declaration change と
  dependent law proof change の同居。
- current prospective approved project-axiom set/digest の通常 proof PR での追加・拡大、terminal actual set の
  current set からの過不足、`proved` から `proved-relative` への silent change。
- R4 freeze 後の全巻 `sorry` 数の増加、新規・未登録 `sorry`、`proved` / `proved-relative` から
  `skeletonized-unproved` への後退、proof body の消失、production import closure への `sorryAx` 混入。
- theorem name、module path、exact type、statement digest の無承認変更。proof PR の import diff に
  future/unproved/sorry-backed module、source-order predecessor でも承認済み `required_by`
  prerequisite でもない ordinary module、current prospective approved set にない `Axioms` module が加わること。
- ordinary assertion stub から intentional axiom への置換、許可 taxonomy・registry・独立承認なしの
  axiom 追加、terminal actual axiom dependency の current prospective approved set からの拡大。
- freeze 後の axiom/set 変更を専用 axiom-policy/statement-dependency PR、source/rationale、user
  approval、independent review、digest update なしに行うこと。これらを満たす controlled exception
  だけが current prospective approved set を更新でき、その専用 PR でも sorry 数増加や frontier
  迂回は禁止する。
- source proof frontier より後の assertion の proof-terminal 遷移、R3 vocabulary freeze 後の無承認
  definition/notation/binder drift、source-order の変更。
- derived assertion の role/edge の silent change、両 role 併記、`consequence` の parent-terminal
  前進行または parent proof からの利用、`prerequisite` の target が遷移時 current proof frontier
  でない先行、dependency cycle、target proof 後に追加された未承認 prerequisite。
- active binding の declaration 不在、未登録 public result、build 対象外 module。

base diff は `content_digest` と disposition-specific digest の一致/不一致、全巻 sorry count、proof
body presence、theorem/module identity、import 増分、production import closure を機械判定する。
assertion の statement digest が不一致なら変更方向にかかわらず通常 PR を止め、dedicated
statement-change PR、source diff、既存 proof result の一時除去、`skeletonized-unproved` への戻し、
独立 source-equivalence approval を要求する。その review で仮定の強化・結論の弱化・
量化域縮小等を semantic regression と分類し default reject する。仮定の弱化、結論の強化、
量化域拡大等も digest change であり同じ専用 PR と review を必須とするが、それだけを理由に
semantic regression とは分類しない。semantic foundation の definition を変える場合は
dedicated breaking-foundation PR とし、Lean constant dependency graph による transitive impact
closure、影響する全 statement/result、semantic tests、full build を提示する。proof PR と
混ぜない。definition/notation/binder/metadata digest の変更も dedicated disposition-change PR と
dependent assertion の impact closure を要求する。

`rewrite-main` は protected branch とし、direct push と force push を禁止する。production/skeleton
build、census、closed-tree、layer、unresolved-registry/declaration/module/direct-body-sorry bijection、
sorry monotonicity、proof-import eligibility、environment axiom、
全 declaration doc-comment、monotonicity check を required にする。`.github/CODEOWNERS` で
vocabulary/skeleton/statement change と assertion proof に独立 reviewer を要求する。人間向け status は常に生成物で、
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

設計承認後の一つの bootstrap PR で、旧 `LatticeSystem/**` の production code と tests、
`LatticeSystem/Tests.lean`、root tip aggregator `LatticeSystem.lean`、`docs/**`、
`formalization-status/**`、`scripts/**`、`tex/**`、legacy workflows、status/schema/retirement/cutover
machinery、site generator を全面削除する。旧内容は main anchor SHA からだけ参照し、新 tree に
archive/copy を残さない。

byte-for-byte 保持を許す実装関連 file は `lean-toolchain` と `lake-manifest.json` だけである。
`lakefile.toml`、`.gitignore`、`README.md`、root `LatticeSystem.lean`、CI は scratch rewrite する。
project governance の `AGENTS.md`、`CLAUDE.local.md`、`LICENSE` と git metadata は保持対象だが、
`CLAUDE.local.md` は本 phase policy に更新する。承認済み本設計は root `DESIGN.md` へ移す。
R1 head の concrete closed-tree allowlist は次の通りとする。

```text
.github/CODEOWNERS
.github/workflows/lean_action_ci.yml
.gitignore
AGENTS.md
CLAUDE.local.md
DESIGN.md
LICENSE
README.md
LatticeSystem.lean
blueprint/schema.json
blueprint/tasaki-2020/source-index.json
lake-manifest.json
lakefile.toml
lean-toolchain
references/tasaki-2020.json
scripts/check_blueprint.py
scripts/check_base_diff.py
scripts/check_closed_tree.py
scripts/check_layers.py
scripts/check_lean_environment.lean
scripts/check_doc_comments.lean
scripts/check_skeleton.py
scripts/fixtures/blueprint-valid-empty.json
scripts/fixtures/blueprint-invalid-duplicate-id.json
scripts/fixtures/doc-comments-valid.lean
scripts/fixtures/doc-comments-invalid-private.lean
scripts/fixtures/doc-comments-invalid-public.lean
scripts/fixtures/skeleton-valid-empty.json
scripts/fixtures/skeleton-invalid-unregistered-sorry.json
scripts/fixtures/skeleton-invalid-transitive-only-sorry.json
scripts/fixtures/skeleton-invalid-production-import.json
scripts/fixtures/skeleton-invalid-future-import.json
scripts/fixtures/skeleton-invalid-unproved-import.json
scripts/fixtures/skeleton-invalid-sorry-backed-import.json
scripts/fixtures/axiom-valid-prospective-unused.json
scripts/fixtures/axiom-valid-terminal-exact.json
scripts/fixtures/axiom-invalid-stub-artificial-reference.json
scripts/fixtures/axiom-invalid-terminal-mismatch.json
scripts/fixtures/axiom-invalid-unapproved-import.json
scripts/fixtures/frontier-valid-current-prerequisite.json
scripts/fixtures/frontier-invalid-early-consequence.json
scripts/fixtures/frontier-invalid-future-prerequisite.json
scripts/fixtures/frontier-invalid-cyclic-prerequisite.json
scripts/fixtures/frontier-valid-completed-prerequisite.json
```

`.git/**` は repository metadata であり tracked allowlist 外で保持する。`docs/` と `tex/` は
directory ごと不在でなければならない。後続 phase の `LatticeSystem/**` source、binding shard、
checker extension は machine manifest と phase-specific allowlist change によってだけ追加する。
この PR は「削除だけ」を一時 merge して後続 PR で直す二段階にせず、最終 tree で次を同時に成立させる。

- package identity、`lean-toolchain`、依存を変えない最小 `lakefile.toml` / manifest。
- public root `LatticeSystem.lean`。DAG tip aggregator ではなく、bootstrap 時点の空の stable
  surface を表す。
- default build target と、checker を含む CI target。
- import layer rule を検査する dependency-free checker。
- empty blueprint から開始できる atomic-claim/slice schema、closed-tree check、layer check、
  actual-axiom checker、disposition-aware base-diff/source-proof-frontier monotonicity check。
  schema/checker は derived assertion の `consequence` / `prerequisite` role、排他的 edge、parent
  terminal/source-order passage、遷移時 target=base current proof frontier、immutable eligibility history、dependency
  DAG acyclicity を初期状態から扱う。
- `mathlibStandardSet` / `warningAsError` とは別に、全 build 対象 module の environment を走査し、
  public/private を含む全 project declaration へ `docBlame` / `docBlameThm` / `#lint` 相当を
  適用する `check_doc_comments`。欠落 doc comment は CI error とし、private helper も例外にしない。
- unresolved registry entry、theorem declaration/module、direct-body `sorryAx` occurrence の exact
  bijection、各 direct count exactly 1、transitive-only rejection、production import isolation、
  proof-import eligibility、局所 sorry-warning 例外を構文+environment で検査する phase-aware
  `check_skeleton` と正負 fixture。actual axiom set は `sorryAx` の有無だけを検査し、個別対応に使わない。
- prospective approved project-axiom metadata/set digest と proof-terminal actual set を phase-aware に
  分離し、stub の unused import/人工参照、terminal mismatch、未承認 Axioms import、通常 proof PR
  での set expansion を拒否する actual-axiom checker と正負 fixture。checker/base-diff は current
  prospective approved set を、R4 で freeze 済み、または freeze 後の専用 axiom-policy/
  statement-dependency PR で source/rationale/user approval/independent review/digest update 済みの
  集合だけとして再構成する。
- allowlist 外 path、`docs/`、`tex/`、legacy artifact を拒否する `check_closed_tree` と正負 fixture。
- `CLAUDE.local.md` に rewrite-main phase override を明記する。すなわち (a) `docs/` / `tex/` は
  明示的な将来承認まで禁止、(b) registry-bound skeleton sorry だけを R4 skeleton target で許し
  production は no-sorry、(c) legacy catalogue/capstone/status は authority でなく新 blueprint と
  Lean environment だけが authority、(d) legacy code は anchor から failure lesson/数学的 idea の
  照合にだけ用い、実装入力は Tasaki 原典と mathlib に限る。
- `README.md` の最小 project identity、build command、legacy anchor、新 trunk の説明。
- tracked `references/tasaki-2020.json` に edition、ISBN/DOI、chapter/section/page range、
  source fingerprint metadata だけを保持する。本の source copy、PDF、抽出 text は tracked
  せず、build、CI、review、再開の依存にしない。
- `.github/workflows/lean_action_ci.yml` の push branch を `main` から `rewrite-main` へ変更し、
  pull request でも同じ build/check を実行する。
- `README.md` / `DESIGN.md` の link は相対 link を優先し、legacy 証跡だけは anchor SHA の
  permalink を使う。`/blob/main/` を新系列の current link として残さない。

削除 scope は bootstrap PR 内で read-only inventory を取り、legacy anchor から常に参照
できることを確認する。bootstrap PR の最終 head は `lake build`、closed-tree、layer、
empty-blueprint、actual-axiom、全 declaration doc-comment、direct-body skeleton isolation/bijection と
proof-import eligibility check を
すべて通す。checker 自体は doc comment あり/なしの private/public fixture、closed-tree と
skeleton の正負 fixture に加え、valid current prerequisite、early consequence、
future-target/cyclic prerequisite、completed-history prerequisite の fixture で fail/pass を検証する。
途中の壊れた commit を trunk に置かず、
atomic PR 全体だけを merge する。

旧 API への compatibility shim、deprecated alias、facade は作らない。旧 proof idea を照合する時は
`git show 01bcb49d49db92c225cfa74b74d409dd0a9c4edc:<path>` 等で読み、新 source から
import せず、code を copy せず、API dependency にせず、commit/file を cherry-pick しない。
これは法的な clean-room 主張ではなく、品質回復のための complete reset / scratch rewrite である。

### R2: whole-book two-pass census and hash lock

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
  append-only/tombstone policy、disposition-aware base-diff/source-proof-frontier checker を有効にする。

R2 が完了するまで数学定義・statement/skeleton・proof の実装 PR を開始しない。census は chapter ごとの
reviewable PR に分割してよいが、最後の freeze gate が通るまでは全て inventory work である。

### R3: whole-book source vocabulary/type layer

- hash-lock した全巻 assertion の exact type を表現するために必要な source vocabulary、canonical
  carrier、definition、structure、notation を Tasaki 原典と mathlib だけから scratch 実装する。
- definition/notation は実 declaration、hypothesis/domain は各 consumer の binder/metadata binding、
  conjecture/out-of-scope は disposition-specific nonproof terminal にする。well-definedness 等の
  proof obligation は別 assertion ID とし、この phase で証明しない。
- Chapter 2--11、Appendix A、Solutions の statement typing に必要な最小 layer を全巻について
  完成させるが、proof body、legacy API shim、将来一般化、未使用 helper は作らない。
- public/private 全 declaration の doc-comment gate、layer/closed-tree/actual-axiom check を通し、
  vocabulary/declaration/binder digest を freeze する。

### R4: whole-book typed assertion skeleton and freeze

- 全 atomic assertion を exact theorem statement `:= by sorry` として細粒度の独立 module に置く。
  全 stub の doc comment に stable claim ID と完全 source locator を記載する。
- skeleton build target は全 stub を型検査するが、production root/import closure から完全隔離する。
  unresolved assertion registry entry、stub theorem declaration、module path、declaration value の direct
  `sorryAx` occurrence を exact bijection にし、各 stub の direct occurrence は exactly 1 とする。
  transitive-only `sorryAx` dependency は stub として認めず、actual axiom set は `sorryAx` の有無だけを
  検査する。source syntax と elaborated environment の双方で照合する。
- stub は statement typing に必要な shared vocabulary だけを import する。prospective approved
  project-axiom set は source/rationale/approval/set digest を持つ metadata として freeze するが、stub
  actual dependency との一致を要求せず、unused `Axioms` import や人工参照を置かない。
- manifest-bound stub の sorry warning だけを局所許容し、その他の warning、未登録 `sorry`、
  `admit`、`native_decide`、intentional axiom への逃避を reject する。
- source-equivalence、仮定強度、quantifier order、non-vacuity plan、statement digest を assertion
  ごとに独立 review して freeze する。この acceptance 前に proof PR を一件も開始しない。

### R5 onward: front-to-back proof discharge

R4 freeze 後、最古の source proof frontier assertion から印刷順に、theorem name、module path、
exact statement/type、digest を変えず proof body を置換する。proof に必要な import は、その時点で
既 proved かつ transitive `sorryAx`-free の source-order predecessor、または current frontier への
承認済み `required_by` を持ち先に discharge 済みの prerequisite module だけ追加できる。
ordinary import と分離して、current prospective approved set、すなわち R4 で freeze 済み、または
freeze 後の専用 axiom-policy/statement-dependency PR で source/rationale/user approval/independent
review/digest update 済みの集合に列挙された exact `Axioms` module だけは追加できる。
future/unproved/sorry-backed ordinary module と未承認 axiom
module は禁止し、base-diff、layer、environment checker の三者で検査する。proof 後は actual project
axiom dependency set が current prospective approved set と exact equality、direct/transitive `sorryAx` が zero
でなければ terminal にしない。project axiom set が空なら `proved`、非空なら `proved-relative` とする。
current prospective approved set にない axiom が必要と判明したら proof PR を停止し、専用
axiom-policy/statement-dependency PR で source/rationale/user approval/independent review/digest
update を完了するまで import/registry を変更しない。更新後の current set は利用できるが、その
専用 PR でも sorry 増加や frontier 迂回はできない。
derived `prerequisite` は current frontier の backward chain に必要で `required_by` と非巡回 DAG を
持つ場合だけ先に proof discharge できる。`consequence` は
全 `derived_from` parent の required terminal と source-order passage 後だけ discharge できる。
どちらも source frontier を進めない。各 proof の actual axiom set を検査し、非空なら
`proved-relative` として axiom-free `proved` と別集計する。

### R6: chapter audit

chapter milestone では旧 declaration 数でなく frozen source census を基準にする。対象 claim の
未分類、disposition required state 未到達、assertion の `skeletonized-unproved` 残存をゼロにし、
`proved-relative` / `approved-deferred` は axiom-free 完了と別集計する。content/disposition-specific
digest、actual axiom、non-vacuity、orphan、layer、source-proof-frontier history、derived role/edge
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
        law とし、両者の R5 terminal 後に `definition-implemented-with-laws`。proof frontier ineligible。
     2. `TASAKI2020-CLAIM-C02-S01-AXIS-NOTATION`: `notation`。`1,2,3` axis notation と展開先を
        R3 で bind して `notation-implemented`。proof frontier ineligible。
     3. `TASAKI2020-CLAIM-C02-S01-SELFADJOINT-COMPONENTS`: `assertion`。R4 で
        `skeletonized-unproved`、R5 で `proved` / `proved-relative`。最初の proof frontier。
     4. `TASAKI2020-CLAIM-C02-S01-EQ-2.1.1`: `assertion`。R4 で `skeletonized-unproved`、R5 で
        proof-terminal。二番目の proof frontier。
     Levi-Civita symbol は Appendix A.3.1 の notation claim を R3 の必要な非 frontier dependency
     として実現し、slice member や独立 assertion を捏造しない。
   - 以後の slice と source assertion frontier は原典順に固定する。
     - **slice 002**: unnumbered Casimir assertion `Ŝ²=S(S+1)1̂`, p. 14。
     - **slice 003**: `TASAKI2020-CLAIM-C02-S01-SPIN-DOMAIN` `domain` record
       (`S=1/2,1,3/2,2,...`)。R3 で consumer binder として `binder-bound` になり、R5 の
       source-order gate がこの record を通過した後だけ
       `LATTICE-DERIVED-SPIN-N-ZERO` `consequence` assertion の R4 stub を proof discharge できる。
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

Appendix の assertion も R4 で全巻 skeletonize するが、proof は本文の current frontier が必要と
する `prerequisite` または Appendix 自身の source frontier に到達するまで先行しない。一般論の
実装は mathlib と照合した必要最小限を `Math` に置く。旧 Theorem 2.4、Chapter 4、AKLT、
Hubbard の完成 proof を先に救出しない。

## Acceptance criteria

### This design PR

- 本ファイルだけが変更されている。
- 基準 SHA と各主要測定値に再測定 command がある。
- Adopt / Rewrite / Drop が file または pattern の根拠付きで分類されている。
- canonical representation、graph/volume boundary、generic local basis、coupling bundle が
  decision として記録されている。
- dependency DAG と初期 directory が一方向である。
- complete reset の closed keep allowlist、`docs/` / `tex/` / legacy status の不存在、新規
  docs/TeX の将来明示承認制、root 文書・blueprint・reference の single-source 関係が確定している。
- axiom の自動移植禁止、専用 path/namespace/taxonomy、defer 境界が明記されている。
- source/derived claim ID と ordered slice ID の分離、disposition-specific binding/digest/status/
  phase eligibility、source-proof frontier、anti-regression policy が明記されている。
- derived assertion が `consequence` / `prerequisite` に排他分類され、parent-terminal と
  current-frontier/acyclic-DAG の eligibility が区別されている。
- assertion だけが skeleton/proof lifecycle を持ち、definition/notation、hypothesis/domain、
  conjecture/out-of-scope がそれぞれ declaration/law、binder、nonproof terminal を持つ。
- unresolved assertion registry entry↔theorem declaration/module↔direct-body `sorryAx` occurrence の
  exact bijection と、proof 昇格時の theorem/module/type/digest 不変・eligible import 増分が明記されている。
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
- 旧 `LatticeSystem/**`、tests、root aggregator、status、旧 scripts/checkers/workflows、legacy TeX、
  site/history/catalogue/docs が final tree に存在せず、同名 path の必要物も scratch rewrite である。
- 既存 code の carry-forward/import/copy/cherry-pick がなく、path 再利用も scratch rewrite である。
- 内容を保持した file が `lean-toolchain` と `lake-manifest.json` だけで、closed-tree check が通る。
- 承認済み設計が root `DESIGN.md` にあり、`docs/` / `tex/` は directory ごと存在しない。
  新規 docs/TeX はユーザーの将来の明示承認なしに追加できない。
- `AGENTS.md`、更新済み `CLAUDE.local.md`、`LICENSE`、git metadata は governance として保持され、
  byte-preserve された実装関連 file は `lean-toolchain` と `lake-manifest.json` だけである。
- package/toolchain は再現可能で、依存更新を混ぜていない。
- minimal `lake build` が warning zero で通る。
- closed-tree、disposition-aware atomic-claim/ordered-slice blueprint schema、layer、phase-aware forbidden
  proof construct、direct-body skeleton bijection/isolation、proof-import eligibility、actual axiom、
  source-proof-frontier monotonicity check がある。
- actual-axiom checker は skeleton の prospective approved metadata と terminal proof の actual set を
  分離し、stub の人工依存、terminal mismatch、未承認 Axioms import、通常 proof PR の set expansion
  を正負 fixture で検査する。
- derived assertion role/edge 排他、consequence parent terminal/source-order passage、prerequisite target=current proof
  frontier（初回遷移時）、immutable eligibility history、dependency DAG 非巡回を検査する
  schema/checker fixture がある。
- public/private を含む全 project declaration を検査する `docBlame` / `docBlameThm` / `#lint`
  相当の専用 doc-comment gate があり、fixture と CI が通る。`mathlibStandardSet` と
  `warningAsError` だけを合格根拠にしない。
- `CLAUDE.local.md` に docs/TeX 禁止、skeleton-phase sorry 例外、production no-sorry、legacy catalogue
  無効化、新 blueprint authority の rewrite-main override が明記され、その正負 fixture が通る。
- public root が DAG tip aggregator ではない。
- CI の push target が `rewrite-main` で、required check が branch protection に登録される。
- `.github/CODEOWNERS` が vocabulary、skeleton/statement、axiom、proof change に独立 reviewer を
  要求し、branch protection がその approval を必須にする。
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

### Whole-book vocabulary/type layer freeze

- 全巻 assertion の exact type を表す最小 vocabulary/type layer が Tasaki 原典と mathlib から
  scratch 実装され、legacy code の copy/import/API dependency がない。
- definition/notation は declaration と必要 law ID、hypothesis/domain は binder/metadata、
  conjecture/out-of-scope は nonproof terminal を持つ。proof を要する law は独立 assertion ID である。
- public/private 全 declaration の doc-comment gate、closed-tree、layer、actual axiom check が通り、
  declaration/binder digest が freeze される。assertion proof body はまだ存在しない。

### Whole-book assertion skeleton freeze

- Chapter 2--11、Appendix A、Solutions の全 atomic assertion が exact theorem `:= by sorry` として
  独立した細粒度 module にある。unresolved registry entry↔theorem declaration↔module path↔その
  declaration value の direct `sorryAx` occurrence が exact bijection で、各 stub の direct count は
  exactly 1、transitive-only dependency はゼロである。
- 各 stub の doc comment に stable claim ID、書名、edition、section、printed/PDF page、
  theorem/equation/problem/subclaim locator が揃う。
- skeleton build は全 stub を型検査し、production root/import closure は unresolved stub module と
  transitive `sorryAx` を含まない。actual axiom set は `sorryAx` の有無を検査し、個別対応は
  declaration body/module mapping で検査する。局所許容された sorry warning 以外は warning zero である。
- 各 assertion の prospective approved project-axiom set が、空集合を含め source/rationale/user
  approval/independent review/set digest とともに freeze される。stub はその project axiom への
  actual dependency 一致を要求されず、unused `Axioms` import/人工参照がない。
- statement digest、source-equivalence、仮定強度、quantifier order、non-vacuity plan が独立 review
  で freeze され、全巻 stub count と registry count が一致する。
- この acceptance 前に proof PR が一件も開始されていない。

### First proof slice

- slice ID は `TASAKI2020-SLICE-C02-S01-001` で、R2 で freeze した ordered member claim 以外を
  含まない。各 member が固有 binding/status/digest/frontier eligibility を持ち、slice 全体の
  `ItemStatement` や手編集 status は存在しない。
- ordered member は `SPIN-OPERATOR` definition → `AXIS-NOTATION` notation →
  `SELFADJOINT-COMPONENTS` assertion → `EQ-2.1.1` assertion。前二者は R3 で declaration binding
  を得て、後二者は R4 で skeletonized-unproved になる。R5 は後二者をこの順に discharge し、
  両者 terminal 後に spin definition が `definition-implemented-with-laws` となる。
- 次の source record は slice 002 Casimir assertion、slice 003 `S=1/2,1,...` domain、slice 004
  dimension assertion。`N=0` は `consequence` derived assertion であり、domain が `binder-bound`
  terminal に到達し、R5 source-order gate がその domain record を通過した後だけ proof eligible で、
  source frontier を進めない。
- `m(k)=N/2-k`、`k=0` highest、`k=N` lowest、row=output/column=input は derived concrete
  representation choice として doc comment と semantic test に記録する。
- legacy endpoint row lemma の名称・物理解釈を移植せず、`S⁺` highest / `S⁻` lowest annihilation
  は basis-vector column action として検査する。
- R5 の最初の proof PR は theorem name/module path/type/digest を保って body を source order で
  置換する。追加 import は既 proved かつ transitive `sorryAx`-free の先行/prerequisite module に
  限る。別枠の `Axioms` import は current prospective approved set、すなわち R4 で freeze 済み、
  または freeze 後の専用 axiom-policy/statement-dependency PR で source/rationale/user approval/
  independent review/digest update 済みの集合の exact module に限り、
  many-body、graph、rotation、future helper を含めない。

### Each proof PR

- proof-eligible assertion のみを対象にし、凍結済み statement digest を変えていない。
- theorem name/module path が不変で、proof type が対応 assertion と definitionally equal である。
- derived prerequisite を含む場合、`required_by` target が遷移時の current source proof frontier、
  dependency DAG が非巡回で、prerequisite 側から target declaration/proof への依存がない。
  consequence を先行利用していない。
- final line から必要性を説明できない declaration がない。
- production build warning zero、禁止 proof construct zero、direct/transitive `sorryAx` zero、actual
  project axiom set = current prospective approved set の exact equality に合格。空なら `proved`、
  非空なら `proved-relative` である。skeleton build の残存 sorry count は base 以下である。
- import diff は既 proved かつ transitive `sorryAx`-free の source-order predecessor または承認済み
  `required_by` prerequisite の ordinary module、または current prospective approved set に列挙済みの
  exact `Axioms` module だけで、future/unproved/sorry-backed/未承認 dependency がない。current set は
  R4 freeze 済み、または freeze 後の専用 axiom-policy/statement-dependency PR で source/rationale/
  user approval/independent review/digest update 済みの集合に限る。
- 通常 proof PR 内で current prospective approved set/digest を変更していない。追加・拡大が必要なら
  proof PR を止め、上記専用 PR で controlled update する。
- unrelated atomic claim、future helper、compatibility work を含まない。
- orphan declaration がなく、status が environment から正しく生成される。
- public/private を含む全 declaration の doc-comment gate と closed-tree check に合格する。
- independent verification review に合格する。

### Chapter 2 milestone

- §2.1--§2.5 の atomic source claim が印刷順に追跡可能である。
- spin-half と general-spin の many-body kernel が一つである。
- graph の有限性と finite volume の有限性が分離されている。
- public theorem が proof-route helper や `Matrix.toLin'` を露出しない。
- 旧 source を import せず、旧実装と同等の対象 statement を新 axiom policy 下で再現する。
- Chapter 2 census の未分類、disposition required state 未到達、assertion の `skeletonized-unproved`
  がゼロである。
- derived assertion の role/edge mismatch、未完 prerequisite、parent 前 consequence がゼロである。
- `proved-relative` / `approved-deferred` が axiom-free `proved` と別集計される。

## P0 decision register

以下をすべて **decided** とする。未決 P0 はゼロである。

1. **trunk**: 新 trunk は `rewrite-main`。bootstrap merge 後に repository default を
   `rewrite-main` とし、production/skeleton build、closed-tree、layer、status、stub/sorry、axiom、
   doc-comment checks を required にする。direct/force push を禁止し、CODEOWNERS の独立 review を
   必須にする。旧 `main` は
   anchor `01bcb49d49db92c225cfa74b74d409dd0a9c4edc` を含む frozen legacy として保護する。
2. **package / namespace**: package name と root namespace `LatticeSystem` は維持する。
   旧 declaration/import path の互換性は維持しない。
3. **complete reset allowlist**: 旧内容を保持するのは `lean-toolchain` と
   `lake-manifest.json` のみ。旧 code/tests/status/scripts/workflows/legacy TeX/docs は全面削除し、
   再利用 path も scratch rewrite。AGENTS/CLAUDE/LICENSE/git metadata は governance として保持し、
   CLAUDE は phase policy に更新する。承認済み設計は root `DESIGN.md` に移す。`docs/` / `tex/`
   は不在とし、新規 docs/TeX はユーザーの将来の明示承認まで禁止する。
4. **blueprint / generated status**: source/derived atomic claim ID と implementation slice ID を
   分離する。番号付き数式、unnumbered obligation、独立結論ごとに source-order key、二 locator、
   disposition、`content_digest`、disposition-specific binding/digest/status/phase eligibility を持つ。
   assertion だけが exact theorem skeleton/proof binding を持ち、definition/notation は declaration/law、
   hypothesis/domain は binder、conjecture/out-of-scope は nonproof terminal を持つ。slice は claim ID
   の順序付き list だけを持ち、独自 statement/status 正本にしない。source-proof frontier と
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
   eq. (2.1.1) assertion。続いて slice 002 Casimir assertion → slice 003 `S=1/2,1,...` domain record →
   slice 004 dimension assertion → eqs. (2.1.2), (2.1.3) を原典順に進める。`N=0` derived assertion
   は R4 で skeletonize しても `consequence` であり、domain の `binder-bound` terminal と
   source-order passage の後だけ proof eligible で
   source frontier を進めない。
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
    blueprint/direct-body-skeleton-bijection/proof-import/phase-aware prospective-vs-actual axiom/
    monotonicity checks、および private を含む全 declaration の
    `docBlame` / `docBlameThm` / `#lint` 相当 gate、`rewrite-main` CI を同時成立させる。
    `CLAUDE.local.md` の phase override と closed-tree fixture を含め、書誌・hash metadata のみ
    tracked し、本の source copy を置かない。
14. **disposition lifecycle**: assertion を `catalogued → skeletonized-unproved (sorryAx) →
    proved/proved-relative` とし、whole-book skeleton freeze 後にだけ proof PR を開始する。
    definition/notation は declaration
    と必要 law、hypothesis/domain は binder binding、conjecture/out-of-scope は nonproof terminal。
    derived consequence は parent terminal と source-order passage 後、derived prerequisite は遷移時 base current source
    proof frontier への required-by、immutable eligibility history、非巡回 DAG の下だけで先行可。
    derived stub の型検査は R4 で可能だが proof eligibility はこの rule に従う。登録 skeleton 以外の
    `sorry` と temporary axiom は使わない。各 unresolved theorem の elaborated value は direct
    `sorryAx` を exactly 1 持ち、transitive-only dependency は stub として数えない。proved declaration
    は direct/transitive とも zero とする。actual axiom set は共通 `sorryAx` の有無を検査し、
    claim ごとの対応は declaration body/module mapping で検査する。
    prospective approved project-axiom set は R4 で source/rationale/approval/digest として freeze し、
    stub に actual 一致や人工参照を要求しない。current set はこの freeze 済み集合、または freeze 後の
    専用 axiom-policy/statement-dependency PR で source/rationale/user approval/independent review/
    digest update 済みの集合だけとする。R5 terminal でだけ current prospective approved=actual を要求し、
    empty/nonempty により `proved` / `proved-relative` を生成する。
    stable claim ID は append-only+tombstone/supersession とする。
15. **axiom isolation**: `LatticeSystem/Axioms/**` は空から始め、閉じた taxonomy、path/namespace、
    directional import、exact registry/environment gate を強制する。`proved` は project axiom
    zero、依存 result は `proved-relative`、axiom は `approved-deferred`。列挙外の解析的対象は
    独立 design PR で新 category/path が承認されるまで axiom 化しない。ordinary stub の axiom
    置換は禁止し、全 terminal proof の actual axiom set と current prospective approved set の exact equality、
    transitive `sorryAx` zero を検査する。freeze 後の新 axiom/set expansion は通常 proof PR で禁止し、
    専用 policy/dependency PR、source/rationale/user approval/independent review/digest update を要求する。
16. **anti-regression / protection**: source deletion、disposition-specific status downgrade、
    content/binding/locator drift、axiom expansion、binding 消失、source-proof-frontier violation
    と、仮定強化・結論弱化・量化域縮小等の semantic regression を base-diff gate で reject する。
    derived role/edge flip、consequence の早期進行、non-current/cyclic prerequisite も reject する。
    R4 freeze 後の sorry 増加、新規/未登録 sorry、proved→sorry、proof 消失、future-frontier proof
    に加え、theorem name/module path/type の drift、future/unproved/sorry-backed import も reject する。
    proof import 追加は既 proved かつ transitive `sorryAx`-free の source-order predecessor または
    approved `required_by` prerequisite の ordinary module に限る。Axioms import は別枠で freeze 済み
    current prospective approved set の exact module だけを許す。current set は R4 freeze 済み、または
    freeze 後の専用 axiom-policy/statement-dependency PR で source/rationale/user approval/
    independent review/digest update 済みの controlled exception に限る。全 digest change は
    disposition に対応する dedicated change PR、source diff、
    独立 review を要求する。
    foundation change は impact closure 付き dedicated PR。`rewrite-main` は direct/force push 禁止、
    independent vocabulary/skeleton/source-equivalence/verification review 必須とする。
17. **source fidelity / basis semantics**: Tasaki の source `domain` claim `S=1/2,1,...` と kernel の
    `consequence` derived assertion `N=0` を分離する。basis は `m(k)=N/2-k`、row=output、column=input。legacy
    `SpinS/Operators.lean` の係数・基底順だけを再照合候補とし、endpoint row lemma の誤名・
    物理解釈は negative evidence として drop する。
18. **minimal documentation boundary**: `docs/` / `tex/` は complete reset で削除して不在にし、
    新規 docs/TeX はユーザーの将来の明示承認まで作らない。root `DESIGN.md` / `README.md`、
    blueprint、references、完全 locator 付き Lean doc comment だけを tracked source trace とし、
    status/frontier は registry と environment から生成する。
19. **phase order**: whole-book two-pass census/hash lock → whole-book source vocabulary/type layer →
    whole-book typed assertion skeleton freeze → front-to-back proof discharge の順を固定し、R4 acceptance
    前の proof PR を禁止する。

## Documentation sync conclusion for this PR

本 PR は review 中の再設計提案一ファイルだけを変更し、現在の実装・公開 status を変更しない。
したがって本 PR では README や旧公開物を同期しない。設計承認後の R1 で legacy `tex/` と旧
docs/status 複製を全面削除し、本設計を root `DESIGN.md` へ移し、README と current branch link
を scratch rewrite する。reset 後は `docs/` / `tex/` を置かず、ユーザーの将来の明示承認なしに
新設しない。以後の status は claim registry/binding と Lean environment からだけ生成する。
