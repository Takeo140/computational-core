License Apache-2.0  Takeo Yamamoto
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic

namespace ButterflyKernel

open Complex

/-- 基数-2 バタフライ順方向カーネル：
    入力 `(a, b)` と回転因子 `ω` から `(a + ω * b, a - ω * b)` を算出する -/
noncomputable def butterflyFwd (ω a b : ℂ) : ℂ × ℂ :=
  (a + ω * b, a - ω * b)

/-- 基数-2 バタフライ逆方向カーネル：
    `(u, v)` と回転因子 `ω`（`ω ≠ 0`）から元の `(a, b)` を復元する -/
noncomputable def butterflyInv (ω u v : ℂ) : ℂ × ℂ :=
  let a := ((1 : ℂ) / 2) * (u + v)
  let b := ((1 : ℂ) / (2 * ω)) * (u - v)
  (a, b)

/-- 順方向カーネルの後に逆方向カーネルを適用すると元の `(a, b)` に戻る（`ω ≠ 0`） -/
theorem butterflyInv_butterflyFwd {ω a b : ℂ} (hω : ω ≠ 0) :
    let uv := butterflyFwd ω a b
    butterflyInv ω uv.1 uv.2 = (a, b) := by
  dsimp [butterflyFwd, butterflyInv]
  ext
  · ring
  · field_simp [hω]
    ring

/-- バタフライ出力の和と差の恒等式（スペクトル成分の対称性・分解の基盤） -/
theorem butterflyFwd_sum_sub (ω a b : ℂ) :
    (butterflyFwd ω a b).1 + (butterflyFwd ω a b).2 = 2 * a ∧
    (butterflyFwd ω a b).1 - (butterflyFwd ω a b).2 = 2 * (ω * b) := by
  simp only [butterflyFwd]
  constructor <;> ring

end ButterflyKernel
