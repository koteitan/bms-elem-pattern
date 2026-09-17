[← Back](README.md) | [English](en/01-ordinals.md) | [Japanese](01-ordinals.md)

# 順序数と ω₁

前提: なし

## 1. 順序数と無限降下列

**定義（整列順序）.** 集合 $`X`$ 上の全順序 $`\lt`$ が **整列順序** であるとは、$`X`$ の空でない部分集合が必ず最小元を持つことをいう。

**定義（順序数）.** 順序数とは整列順序の型である。順序数 $`\alpha`$ は、それより小さい順序数全体 $`\{\beta : \beta \lt \alpha\}`$ と同一視する。以下で「$`\alpha`$ の元」「$`\alpha`$ 未満の順序数」は同じ意味である。

| 順序数 | それより小さい順序数 |
|---|---|
| $`0`$ | なし |
| $`3`$ | $`0, 1, 2`$ |
| $`\omega`$ | $`0, 1, 2, \dots`$ |
| $`\omega + 1`$ | $`0, 1, 2, \dots, \omega`$ |
| $`\omega \cdot 2`$ | $`0, 1, 2, \dots, \omega, \omega + 1, \omega + 2, \dots`$ |

順序数全体も、$`\lt`$ で整列している。

**定理（無限降下列は無い）.** 順序数の列 $`\alpha_0 \gt \alpha_1 \gt \alpha_2 \gt \cdots`$ は存在しない。

**証明.** そういう列があるとして、集合 $`\{\alpha_t : t \in \mathbb{N}\}`$ の最小元を $`\alpha_{t_0}`$ とする。$`\alpha_{t_0 + 1}`$ もこの集合に入り、$`\alpha_{t_0 + 1} \lt \alpha_{t_0}`$ なので、最小性に反する。$`\square`$

停止性の証明は、最後にこの定理に帰着する（[08](08-termination.md)）。

## 2. 後続と、後続で閉じた順序数

**定義.** $`\alpha + 1`$ は $`\alpha`$ より大きい最小の順序数である。$`\alpha = \beta + 1`$ と書ける順序数を **後続順序数**、$`0`$ でも後続順序数でもない順序数を **極限順序数** と呼ぶ。

**定義（後続で閉じる）.** 順序数 $`\alpha`$ が **後続で閉じる** とは、次が成り立つことをいう。

```math
\forall z \lt \alpha\ \ (z + 1 \lt \alpha)
```

後続で閉じることは、$`\alpha = 0`$ または $`\alpha`$ が極限順序数であることと同じである。$`\alpha = \beta + 1`$ なら $`z = \beta`$ で破れるからである。

| $`\alpha`$ | 後続で閉じるか | 理由 |
|---|---|---|
| $`0`$ | 閉じる | $`z \lt 0`$ となる $`z`$ が無い |
| $`3`$ | 閉じない | $`2 + 1 = 3`$ |
| $`\omega`$ | 閉じる | $`n + 1 \lt \omega`$ |
| $`\omega + 1`$ | 閉じない | $`\omega + 1`$ 自身 |
| $`\omega \cdot 2`$ | 閉じる | $`\omega + n + 1 \lt \omega \cdot 2`$ |

以下のノートでは「極限」の代わりにこの言い方を使う。$`0`$ を場合分けしなくて済むからである。

### 2.1 有限個の順序数の上界

**補題.** $`0 \lt \alpha`$ とし、$`x_0, \dots, x_{b-1} \lt \alpha`$ とする。このとき $`z \lt \alpha`$ で、すべての $`i \lt b`$ について $`x_i \le z`$ となるものがある。

**証明.** $`b \gt 0`$ なら $`z = \max_i x_i`$、$`b = 0`$ なら $`z = 0`$ とすればよい。$`\square`$

$`\alpha`$ が後続で閉じるなら $`z + 1 \lt \alpha`$ なので、$`\alpha`$ 未満に、すべての $`x_i`$ より真に大きい順序数がある。

## 3. 可算順序数と ω₁

**定義.** 集合が **可算** であるとは、有限であるか、自然数全体と一対一に対応することをいう。

**定義（ω₁）.** $`\omega_1`$ は、それより小さい順序数全体が可算でない最小の順序数である。$`\Omega_1`$ と書くこともある。

次の 4 つの事実を使う。

**事実 1.** $`\gamma \lt \omega_1`$ と、$`\gamma`$ 未満の順序数全体が可算であることは同値である。

**事実 2.** $`\omega_1`$ は後続で閉じる。$`\gamma`$ 未満の順序数全体が可算なら、$`\gamma + 1`$ 未満の順序数全体も可算だからである。

**事実 3（正則性）.** 可算個の順序数 $`\gamma_i \lt \omega_1`$ の上限は $`\omega_1`$ 未満である。可算個の可算集合の和集合は可算だからである（選択公理を使う）。

**事実 4（数え上げ）.** $`0 \lt \gamma \lt \omega_1`$ なら、自然数から $`\gamma`$ 未満の順序数全体への全射 $`e : \mathbb{N} \to \gamma`$ がある。

事実 4 により、$`\gamma`$ 未満の順序数を並べた有限列は、自然数の有限列で番号づけできる。これを [07](07-closure-chains.md) で使う。

| 順序数 | $`\omega_1`$ 未満か |
|---|---|
| $`\omega`$、$`\omega^2`$、$`\varepsilon_0`$ | 未満 |
| $`\psi_0(\Omega_\omega)`$（ペア数列の順序数） | 未満 |
| $`\omega_1`$ | 未満でない |

## 4. 参考：再帰的順序数と許容順序数

証明には使わないが、ラベルの大きさを論じるときに出てくる。

計算可能な整列順序の型として表せる順序数を **再帰的順序数** と呼び、その上限を $`\omega_1^{\mathrm{CK}}`$ と書く。$`\omega_1^{\mathrm{CK}}`$ は $`\omega`$ より大きい最小の許容順序数であり、$`\omega_1^{\mathrm{CK}} \lt \omega_1`$ である。したがって $`\omega`$ より大きく $`\omega_1^{\mathrm{CK}}`$ より小さい順序数は、許容順序数でない。

## 5. 証明での使われ方

| 事実 | 使う場所 |
|---|---|
| 無限降下列は無い | [08](08-termination.md) 停止性 |
| 後続で閉じる | [04](04-pattern-properties.md) P3、P5、P6 |
| 有限個の順序数の上界 | [04](04-pattern-properties.md) P3、P4 |
| 事実 1〜4 | [07](07-closure-chains.md) 閉包 |

## 6. Lean での対応

| 概念 | Lean | ファイル |
|---|---|---|
| 順序数 | `Ordinal.{0}` | Mathlib |
| $`z + 1`$ | `Order.succ z` | Mathlib |
| 有限個の順序数の上界 | `exists_bound` | [`Pattern/Basic.lean`](../../lean/Pattern/Basic.lean) |
| $`\omega_1`$ | `Om` | [`Pattern/Chain.lean`](../../lean/Pattern/Chain.lean) |
| 事実 1 | `countable_Iio` | 同上 |
| 事実 2 | `om_succ_lt` | 同上 |
| 事実 3 | `Ordinal.iSup_lt_omega_one` | Mathlib |
| 事実 4 | `enumBelow`, `enumBelow_surj` | [`Pattern/Chain.lean`](../../lean/Pattern/Chain.lean) |
| 無限降下列は無い | `WellFounded.has_min` | Mathlib |
