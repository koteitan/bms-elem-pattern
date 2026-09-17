[← Back](README.md) | [English](en/05-finite-reflection.md) | [Japanese](05-finite-reflection.md)

# すべての段の有限反映

前提: [pss 05 配列、展開、安定ラベル](../pss/05-arrays-labels.md) §5、[pss 06 有限反映](../pss/06-finite-reflection.md) §2〜§4、[01](01-cofinal-continuity.md)〜[04](04-cofinal-predecessors.md)

## 1. 主張

$`N \ge 1`$ とし、$`\mathcal{R}_N`$ の関係でラベルの関係を置く。

```math
\lhd_k = \lt_{k+1} \qquad (k \lt N)
```

**定理（有限反映）.** $`n \lt N`$、$`\alpha \lhd_n \beta`$、$`X = \{p_0, \dots, p_{k-1}\} \subseteq \alpha`$、$`\alpha \le y_0 \lt \cdots \lt y_{s-1} \lt \beta`$ とする。このとき $`y'_0 \lt \cdots \lt y'_{s-1} \lt \alpha`$ で、[pss 05](../pss/05-arrays-labels.md) §5 の (a)〜(d) を満たすものがある。(d) は次である。

```math
\forall i \lt s\ \forall m \lt n\ \bigl(y_i \lt_{m+1} \beta \Rightarrow y'_i \lt_{m+1} \alpha\bigr) \qquad \text{(d)}
```

- $`n = 0`$ は [pss 06](../pss/06-finite-reflection.md) §3 で示した
- 以下 $`n \ge 1`$、つまり $`\alpha \lt_{n+1} \beta`$ とする
- (a)(b)(c) は、$`\vec y' \lt \alpha`$ で $`\mathrm{diag}(\vec p, \vec y') = \mathrm{diag}(\vec p, \vec y)`$ となるものを取れば、[pss 06](../pss/06-finite-reflection.md) §2 の補題から出る

## 2. 文

$`i \lt s`$ ごとに $`M_i = \{m \lt n : y_i \lt_{m+1} \beta\}`$ と置く。長さ $`s`$ の組 $`\vec U`$、$`\vec V`$ について、次の文 $`\sigma`$ を使う。パラメータは $`\vec p`$ である。

```math
\sigma = \exists \vec U\ \forall \vec V\ \Bigl(\mathrm{diag}(\vec p, \vec U) = \mathrm{diag}(\vec p, \vec y) \wedge \bigwedge_{i \lt s} \bigl(U_i \le V_i \wedge \Phi_{n-1}(V_i) \Rightarrow \bigwedge_{m \in M_i} U_i \le_{m+1} V_i\bigr)\Bigr)
```

- $`M_i`$ は外で決まる集合で、どの連言を入れるかの選択である。式の一部ではない
- $`\Phi_{n-1}`$ は $`\Pi_{n-1}`$（$`n = 1`$ なら真）なので、$`\bigwedge_i`$ の中身は $`\Sigma_{n-1}`$ 論理式。$`\forall \vec V`$ で $`\Pi_n`$、$`\exists \vec U`$ で $`\Sigma_{n+1}`$ になる
- Lean の形では、[03](03-block-form.md) §4 (3) のとおりブロック $`[s, s, \dots, s]`$（$`n + 1`$ 個）で書ける
- $`n = 1`$ のとき、$`\sigma`$ は [pss 06](../pss/06-finite-reflection.md) §4 の文と同じである

**考え方.** $`\Phi_{n-1}(V_i)`$ は、$`V_i`$ が上端に $`\le_{n-1}`$ で結ばれていることを中から言っている（[02](02-phi.md) §5）。上端に結ばれた $`V_i \ge U_i`$ のすべてに $`U_i`$ が $`\le_{m+1}`$ で結ばれていれば、P4′ で $`U_i`$ も上端に $`\le_{m+1}`$ で結ばれる。

## 3. β で真

$`\vec U = \vec y`$ と置く。原子図式の一致は明らか。$`\vec V \lt \beta`$、$`i \lt s`$ を取り、$`y_i \le V_i`$、$`\beta \models \Phi_{n-1}(V_i)`$、$`m \in M_i`$ とする。$`y_i \le_{m+1} V_i`$ を示す。

1. $`V_i \le_m \beta`$ を示す。$`m = 0`$ なら $`V_i \lt \beta`$ から明らか。$`m \ge 1`$ なら $`n \ge 2`$ である。$`\alpha \lt_2 \beta`$ なので P6 から $`\beta`$ は後続で閉じ、補題 A から $`V_i \le_{n-1} \beta`$。$`m \le n - 1`$ なので $`V_i \le_m \beta`$
2. $`m \in M_i`$ から $`y_i \le_{m+1} \beta`$
3. $`y_i \le V_i \le \beta`$ なので、[01](01-cofinal-continuity.md) §4 の系を $`u = y_i`$、$`s = V_i`$、$`\gamma = \beta`$ で使うと $`y_i \le_{m+1} V_i`$

$`\square`$

## 4. α で (d)

$`\alpha \le_{n+1} \beta`$、$`\vec p \lt \alpha`$ なので、$`\sigma`$ は $`\alpha`$ でも真である。証人を $`\vec y'`$ とする。

- $`\vec V`$ に何を入れても原子図式の一致が要るので、$`\mathrm{diag}(\vec p, \vec y') = \mathrm{diag}(\vec p, \vec y)`$。§1 から (a)(b)(c) が出る
- (d) を示す。$`i \lt s`$、$`m \in M_i`$ を取る。$`y'_i \le_{m+1} \alpha`$ を、P4′ を $`j = m + 1`$ で使って示す

**点 v の取り方.** $`z \lt \alpha`$ を取り、$`z' = \max(z, y'_i)`$ と置く。次を満たす $`v`$ を取る。

```math
z' \lt v \lt \alpha, \qquad \alpha \models \Phi_{n-1}(v), \qquad n \ge 2 \Rightarrow v \le_{n-1} \alpha
```

- $`n = 1`$ のとき：$`v = z' + 1`$。$`\alpha \lt_1 \beta`$ なので P5 から $`\alpha`$ は後続で閉じ、$`v \lt \alpha`$。$`\Phi_0`$ は真
- $`n \ge 2`$ のとき：$`\alpha \lt_n \beta`$ なので、P7′（[04](04-cofinal-predecessors.md)）から $`l \le n - 1`$ のすべてで $`\mathrm{Cof}_l(\alpha)`$。$`\mathrm{Cof}_{n-1}(\alpha)`$ から $`z' \lt v \lt \alpha`$、$`v \le_{n-1} \alpha`$ となる $`v`$ を取る。補題 B から $`\alpha \models \Phi_{n-1}(v)`$

**v が P4′ の条件を満たす.**

1. $`\sigma`$ の $`\forall \vec V`$ に、すべての成分が $`v`$ の組を入れる。$`y'_i \le v`$ と $`\alpha \models \Phi_{n-1}(v)`$ から、$`y'_i \le_{m+1} v`$
2. $`v \le_{m-1} \alpha`$ を示す。$`m \le 1`$ なら自動的に成り立つ。$`m \ge 2`$ なら $`n \ge m + 1 \ge 3`$ なので $`v \le_{n-1} \alpha`$ で、$`m - 1 \le n - 1`$ から $`v \le_{m-1} \alpha`$

こうして取った $`v`$ の全体を $`S`$ とすると、$`S \subseteq [y'_i, \alpha)`$ は $`\alpha`$ で非有界で、P4′ の条件を満たす。したがって $`y'_i \le_{m+1} \alpha`$。$`y'_i \lt \alpha`$ なので $`y'_i \lt_{m+1} \alpha`$。

$`\square`$

## 5. ラベルの体系

**系.** $`N \ge 1`$ のとき、$`\mathrm{Lab}`$ を順序数全体とし、$`\lhd_k = \lt_{k+1}`$（$`k \lt N`$）と置くと、これは行数 $`N`$ のラベルの体系（[pss 05](../pss/05-arrays-labels.md) §5）である。

- 狭義、推移：[pss 03](../pss/03-patterns.md) §3
- 有限反映：$`n = 0`$ は [pss 06](../pss/06-finite-reflection.md) §3、$`n \ge 1`$ は §1〜§4

## 6. 3 行の証明との違い

[pss 06](../pss/06-finite-reflection.md) §5 の $`n = 2`$ の証明は、$`\vec v`$ に $`\le_1`$ で結ばれた点を入れ、$`\le_1`$ が切れる点 $`w_i`$ があるかどうかで場合分けした。この方法を段 3 以上に広げるには P4 を段 3 以上で使う必要があり、そこで止まっていた（[pss 06](../pss/06-finite-reflection.md) §6）。

ここでは、次の 2 つでこれを避けている。

- $`\vec V`$ に「上端に結ばれている」という仮定 $`\Phi_{n-1}(V_i)`$ を付ける。$`\beta`$ で真であることは、[01](01-cofinal-continuity.md) の系だけで示せる
- $`\alpha`$ の側では、$`v`$ を $`\mathrm{Cof}_{n-1}(\alpha)`$ から取る。すると $`v \le_{n-1} \alpha`$ なので、P4′ の追加の条件 $`v \le_{m-1} \alpha`$ が満たされる

## 7. 証明での使われ方

| 事実 | 使う場所 |
|---|---|
| §5 のラベルの体系 | [06](06-termination.md) で命題 19.1 に渡す |

## 8. Lean での対応

`reflect_gen hn1 h` の仮定 `lab N n α β` は $`\alpha \lt_{n+1} \beta`$ である。結論の `SameBits` が原子図式の一致、最後の条件が (d) である。

| 概念 | Lean | ファイル |
|---|---|---|
| §2 の $`\sigma`$ の意味 | `reflect_gen` の中の `hsem` | [`Pattern/General.lean`](../../lean/Pattern/General.lean) |
| §3 | `reflect_gen` の中の `hβsat` | 同上 |
| §4 | `reflect_gen` | 同上 |
| ブロックが 0 個の一致 | `elem_zero` | 同上 |
| $`v \le_{j} \alpha`$ から $`\Sigma_i`$ の一致（$`i \le j`$） | `elem_of_lev` | 同上 |
| §5 | `labelSystemGen` | 同上 |
| $`n = 0`$ | `reflect_zero` | [`Pattern/Reflect.lean`](../../lean/Pattern/Reflect.lean) |
| [pss 06](../pss/06-finite-reflection.md) §2 の補題 | `copy_props` | 同上 |
