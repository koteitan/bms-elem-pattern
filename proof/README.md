# Σ₂ 初等部分構造によるペア数列システムの停止性の証明

ペア数列の展開がいつか必ず止まることを、Carlson の構造 $`\mathcal{R}_2`$ の関係をラベルに使って Lean 4 で証明した。
ラベルの関係の定義には、構成可能階層も許容順序数も使っていない。

## 結論

**定理（停止性）.** $`A`$ をペア数列、$`n : \mathbb{N} \to \mathbb{N}`$ を任意の関数とし、

```math
A_0 = A, \qquad A_{t+1} = A_t[n(t)]
```

と置く。このとき、ある $`T`$ で $`A_T`$ は空である。

**定理（整礎性）.** ペア数列の上の関係

```math
A \mathrel{R} B \iff B \ne \emptyset \wedge \exists n\ \bigl(A = B[n]\bigr)
```

は整礎である。

Lean の証明に `sorry` は無く、公理は `propext` / `Classical.choice` / `Quot.sound` のみ。

## 1. ペア数列

展開規則は BM4 の 2 行版で、[koteitan/dh-bms-wf-formal](https://github.com/koteitan/dh-bms-wf-formal) の展開をそのまま使う。

BM4 の初期列 $`E_2 = (0,0)(1,1)`$ から届くのは $`\varepsilon_0`$ 未満だけなので、初期列を次のように広げた。

```math
S_n = (0,0)(1,1)\cdots(n,n)
```

**定義.** ペア数列とは、ある $`S_n`$ から展開を有限回して得られる 2 行の配列のことである。

## 2. 証明の骨格

DH の証明と同じく、列ごとに順序数のラベルを 1 つ貼り、展開するとコピーには元より小さいラベルが付くことで、最後の列のラベル（高さ）が下がることを示す。
DH との違いは、ラベルの関係 $`\lhd_k`$ を構成可能階層の初等部分構造ではなく、$`\mathcal{R}_2`$ の関係で与えることである。

```mermaid
flowchart TB
  A["R2 の定義"] --> B["有限反映 n=0,1"]
  A --> C["<₂ 鎖の存在"]
  B --> D["命題 19.1"]
  C --> E["初期列のラベル"]
  D --> F["高さの下降"]
  E --> F
  F --> G["停止性"]
```

## 3. R2

```math
\mathcal{R}_2 = (\mathrm{Ord}; \le, \le_1, \le_2)
```

```math
\alpha \le_i \beta \iff (\alpha; \le, \le_1, \le_2) \preceq_{\Sigma_i} (\beta; \le, \le_1, \le_2) \qquad (i = 1, 2)
```

```math
\alpha \lt_i \beta \iff \alpha \lt \beta \wedge \alpha \le_i \beta
```

$`\le_1`$ と $`\le_2`$ は、$`\beta`$ についての帰納法で同時に定義する。

Lean では論理式を構文にしない。

- $`n`$ 変数の量化子なし論理式は、$`n`$ 組の原子図式の集合 $`D`$ で表す。$`n`$ 組 $`v`$ の原子図式は、各 $`a, b \lt n`$ に次の真偽の組を対応させるものである。

```math
\mathrm{diag}(v)(a, b) = \bigl( [v_a \le v_b],\ [v_a \le_1 v_b],\ [v_a \le_2 v_b] \bigr)
```

- パラメータ $`\vec p`$ を持つ $`\Sigma_2`$ 文は、次の形で表す。$`\Sigma_1`$ 文は $`\vec y`$ が空の場合である。

```math
M \models \exists \vec x\ \forall \vec y\ \bigl(\mathrm{diag}(\vec p, \vec x, \vec y) \in D\bigr)
```

基本性質：

| 性質 |
|---|
| $`a \le_2 b \Rightarrow a \le_1 b`$ |
| $`\le_1`$ と $`\le_2`$ は推移的 |
| $`a \le b \le c \wedge a \le_1 c \Rightarrow a \le_1 b`$ |
| $`y \le \alpha`$、$`\alpha`$ が後続で閉じ、$`\forall v \in [y, \alpha)\ y \le_1 v`$ $`\Rightarrow y \le_1 \alpha`$ |
| $`\alpha \lt_1 \beta \Rightarrow \forall z \lt \alpha\ (z + 1 \lt \alpha)`$ |

## 4. ラベルの関係と有限反映

```math
\lhd_0 = \lt_1, \qquad \lhd_1 = \lt_2
```

命題 19.1 がラベルに要求するのは、$`\lhd_k`$ が狭義で推移的であることと、次の有限反映だけである。

**有限反映.** $`n \lt 2`$、$`\alpha \lhd_n \beta`$、$`X \subseteq \alpha`$ は有限、$`\alpha \le y_0 \lt \cdots \lt y_{s-1} \lt \beta`$ とする。このとき $`y'_0 \lt \cdots \lt y'_{s-1} \lt \alpha`$ で、次の (a)〜(d) を満たすものがある。

```math
\max X \lt y'_0 \qquad \text{(a)}
```

```math
\forall x \in X\ \forall i \lt s\ \forall k \lt 2\ \bigl(x \lhd_k y_i \Rightarrow x \lhd_k y'_i\bigr) \qquad \text{(b)}
```

```math
\forall i, j \lt s\ \forall k \lt 2\ \bigl(y_i \lhd_k y_j \Rightarrow y'_i \lhd_k y'_j\bigr) \qquad \text{(c)}
```

```math
\forall i \lt s\ \forall m \lt n\ \bigl(y_i \lhd_m \beta \Rightarrow y'_i \lhd_m \alpha\bigr) \qquad \text{(d)}
```

**$`n = 0`$ のとき.** $`\Sigma_1`$ 文「$`X`$ の上に、$`X \cup Y`$ と同じ原子図式を持つ点の組がある」は $`\beta`$ で真なので、$`\alpha \lt_1 \beta`$ により $`\alpha`$ でも真になる。その証人が $`y'`$ で、(a)(b)(c) は原子図式が同じことから出る。(d) は $`m \lt 0`$ なので空である。

**$`n = 1`$ のとき.** 上の文に、$`y_i \lt_1 \beta`$ となる各 $`i`$ について

```math
\forall v\ \bigl(u_i \le v \Rightarrow u_i \le_1 v\bigr)
```

を足した $`\Sigma_2`$ 文を使う。

1. $`\beta`$ で真：$`y_i \le_1 \beta`$ と $`y_i \le v \lt \beta`$ から $`y_i \le_1 v`$
2. $`\alpha \lt_2 \beta`$ により $`\alpha`$ でも真。証人 $`u_i = y'_i`$ は、すべての $`v \in [y'_i, \alpha)`$ で $`y'_i \le_1 v`$
3. $`\alpha`$ は後続で閉じるので、連続性から $`y'_i \lt_1 \alpha`$。これが (d)

これは Wilken の論文 "Pure Σ2-elementarity beyond the core" の補題 1.7 と同じ内容である。

## 5. 初期列のラベル

$`S_n`$ には、長さ $`n+1`$ の $`\lt_2`$ 鎖

```math
c_0 \lt_2 c_1 \lt_2 \cdots \lt_2 c_n
```

をそのままラベルとして貼る。すべての列の組が $`\lt_2`$ で結ばれ、$`\lt_2 \subseteq \lt_1`$ なので、行 0 と行 1 のどちらの祖先関係も満たす。

$`\lt_2`$ 鎖があることは、$`\omega_1`$ の中の閉包で示す。

パラメータが $`\gamma`$ 未満で $`\omega_1`$ で真な $`\Sigma_2`$ 文のそれぞれについて証人を 1 つ選び、その成分に $`+1`$ したもの全体の上限を取る。これと $`\gamma`$ の大きいほうに $`+1`$ したものを $`\mathrm{next}(\gamma)`$ とする。

```math
\lambda(\gamma) = \sup_{t \lt \omega} \mathrm{next}^t(\gamma)
```

このとき次が成り立つ。

```math
\gamma \lt \omega_1 \Rightarrow \gamma \lt \lambda(\gamma) \lt \omega_1
```

```math
\gamma \lt \omega_1 \Rightarrow (\lambda(\gamma); \le, \le_1, \le_2) \preceq_{\Sigma_2} (\omega_1; \le, \le_1, \le_2)
```

```math
\gamma, \delta \lt \omega_1 \wedge \lambda(\gamma) \lt \lambda(\delta) \Rightarrow \lambda(\gamma) \lt_2 \lambda(\delta)
```

```math
\lambda(0) \lt_2 \lambda(\lambda(0)) \lt_2 \lambda(\lambda(\lambda(0))) \lt_2 \cdots
```

- $`\mathrm{next}(\gamma) \lt \omega_1`$ になるのは、論理式とパラメータの組の全体が可算なので、証人の上限が $`\omega_1`$ 未満の順序数の可算個の上限になるからである
- 2 行目は Tarski–Vaught の判定と同じ議論である
  - $`\omega_1`$ で真な $`\Sigma_2`$ 文は、$`\lambda(\gamma)`$ の中に証人を持つ
  - 逆向きは、$`\forall`$ 部分の反例を $`\Sigma_1`$ 文にして、上の事実を使う
- 3 行目は、どちらも $`\omega_1`$ の $`\Sigma_2`$ 初等部分構造であることから出る

## 6. 高さの下降と停止性

配列 $`A`$ の長さを $`\ell`$、ラベルを $`f`$ とするとき、高さを $`\mathrm{ht}(f) = f(\ell - 1)`$ と置く。

**命題 19.1（DH）.** 安定ラベル $`f`$ を持つ空でない配列 $`A`$ と $`N \in \mathbb{N}`$ について、$`A[N]`$ が空でなければ、$`A[N]`$ は安定ラベル $`g`$ で

```math
\mathrm{ht}(g) \lt \mathrm{ht}(f)
```

となるものを持つ。

これは dh-bms-wf-formal で有限反映を仮定して証明されたものを、そのまま使う。

- 空でないペア数列は安定ラベルを持つ。初期列には §5、展開には命題 19.1 を使う
- 展開列が空にならないとすると、命題 19.1 で高さが無限に下がる順序数の列が作れ、順序数の整礎性に反する。これが停止性である
- $`R`$ の無限降下列は展開列の形なので、整礎性は停止性に帰着する

## 7. 形式化していないこと

- **ラベルが小さいこと**
  - Lean の証明は、$`\lt_2`$ 鎖を $`\omega_1`$ の中の閉包で作っているので、ラベルがどれくらいの大きさかは示していない
  - Wilken によれば、有限の $`\le_2`$ 鎖がいくらでも長くとれる最小の順序数は、$`\Pi^1_1\text{-}\mathrm{CA}_0`$ の証明論的順序数 $`\psi_0(\Omega_\omega)`$ である（下の "Tracking chains revisited" の序文）。この場合、ラベルは $`\psi_0(\Omega_\omega)`$ 未満の再帰的順序数に取れて、許容順序数ではない
  - この事実は形式化していない
- **他の版のペア数列との一致**：扱うのは BM4 の 2 行版だけである
- **3 行以上**
  - (d) に $`m = 1`$ の条件 $`y_i \lt_2 \beta \Rightarrow y'_i \lt_2 \alpha`$ が加わる
  - $`\le_2`$ は $`\le`$ に沿っては閉じていないので、§4 の $`n = 1`$ の方法はそのままでは使えない

## 8. Lean との対応

| 数学 | Lean | ファイル |
|---|---|---|
| $`\le_1`$、$`\le_2`$ の定義 | `R2fix`, `le1`, `le2`, `le1_iff`, `le2_iff` | [`R2.lean`](../lean/Wilken/R2.lean) |
| $`\Sigma_2`$ 文、原子図式 | `Sat`, `diag` | 同上 |
| $`a \le_2 b \Rightarrow a \le_1 b`$ | `le1_of_le2` | 同上 |
| 推移律 | `le1_trans`, `le2_trans` | 同上 |
| $`a \le b \le c \wedge a \le_1 c \Rightarrow a \le_1 b`$ | `le1_of_le_of_le1` | 同上 |
| 連続性 | `le1_of_forall` | 同上 |
| $`\alpha \lt_1 \beta`$ なら後続で閉じる | `succ_lt_of_lt1` | 同上 |
| $`\lhd_0`$、$`\lhd_1`$ | `rel` | [`Reflect.lean`](../lean/Wilken/Reflect.lean) |
| 有限反映 $`n = 0`$ | `reflect_zero` | 同上 |
| 有限反映 $`n = 1`$ | `reflect_one` | 同上 |
| ラベルの体系 | `labelSystem` | 同上 |
| $`\mathrm{next}`$、$`\lambda`$ | `next`, `lam` | [`Chain.lean`](../lean/Wilken/Chain.lean) |
| $`\lambda(\gamma) \preceq_{\Sigma_2} \omega_1`$ | `lam_elem` | 同上 |
| $`\lambda(\gamma) \lt_2 \lambda(\delta)`$ | `lt2_lam` | 同上 |
| $`\lt_2`$ 鎖の存在 | `exists_lt2_chain` | 同上 |
| $`S_n`$ | `stair` | [`PSS.lean`](../lean/Wilken/PSS.lean) |
| ペア数列 | `PSS` | 同上 |
| $`S_n`$ のラベル | `stable_stair` | 同上 |
| 空でないペア数列のラベル | `pss_stable` | 同上 |
| 停止性 | `pss_terminates` | 同上 |
| 整礎性 | `PR_wf` | 同上 |
| 命題 19.1 | `descent` | [`Bm4/Label.lean`](../lean/Bm4/Label.lean) |

## 9. ファイル

| ファイル | 行数 | 内容 |
|---|---:|---|
| [`lean/Wilken/R2.lean`](../lean/Wilken/R2.lean) | 280 | $`\mathcal{R}_2`$ の定義と基本性質 |
| [`lean/Wilken/Reflect.lean`](../lean/Wilken/Reflect.lean) | 199 | 有限反映、ラベルの体系 |
| [`lean/Wilken/Chain.lean`](../lean/Wilken/Chain.lean) | 242 | $`\lt_2`$ 鎖の存在 |
| [`lean/Wilken/PSS.lean`](../lean/Wilken/PSS.lean) | 96 | ペア数列の定義、停止性、整礎性 |
| `lean/Bm4/` | 2,923 | BM4 の組合せ部分（配列、展開、コピー補題、命題 19.1） |

`lean/Bm4/` は [koteitan/dh-bms-wf-formal](https://github.com/koteitan/dh-bms-wf-formal) の `lean/Bm4/` から、組合せ部分だけをコピーした。
変更したのは `Label.lean` のラベルの界面だけである。

- 行数 $`r`$ を界面の引数にし、有限反映は $`n \lt r`$ の場合だけを要求する
- 使われていない単調性の条件と、初期列 $`E_r`$ のためだけの初期対の条件を外した

3 行以上では §4 の方法がそのままでは使えない（§7）ので、行数を固定した界面にした。

## 10. ビルド

Lean 4.30.0 と Mathlib v4.30.0 を使う。

```sh
cd lean
lake exe cache get
lake build
```

## 出典

- G. Wilken, Pure Σ2-elementarity beyond the core, Annals of Pure and Applied Logic 172 (2021). https://doi.org/10.1016/j.apal.2021.103001
- G. Wilken, Tracking chains revisited. https://arxiv.org/abs/1611.04348
- G. Wilken, Pure patterns of order 2. https://arxiv.org/abs/1608.08421
- T. J. Carlson and G. Wilken, Tracking chains of Σ2-elementarity, Annals of Pure and Applied Logic 163 (2012).
