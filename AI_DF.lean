License Apache-2.0  Takeo Yamamoto
import Mathlib.Tactic

namespace AIDiscreteVerification

/-- 整数（または固定小数点・量子化スカラー）上の閉区間 `[lo, hi]` -/
structure Interval where
  lo : Int
  hi : Int
  valid : lo ≤ hi
  deriving Repr

/-- 区間 `iv` に値 `x` が含まれること -/
def InInterval (iv : Interval) (x : Int) : Prop :=
  iv.lo ≤ x ∧ x ≤ iv.hi

/-- 単調非減少関数 `f` の定義 -/
def MonotoneInt (f : Int → Int) : Prop :=
  ∀ {a b : Int}, a ≤ b → f a ≤ f b

/-- 1入力・1出力の線形層（重み `w`、バイアス `b`）の離散計算 -/
def linearStep (w b x : Int) : Int :=
  w * x + b

/-- 1入力・1出力の活性化関数（ReLU相当のクリップ関数） -/
def reluClip (cap x : Int) : Int :=
  if x ≤ 0 then 0 else if cap ≤ x then cap else x

/-- `reluClip` が単調非減少であることの証明（`cap ≥ 0` のとき） -/
theorem reluClip_monotone {cap : Int} (hcap : 0 ≤ cap) :
    MonotoneInt (reluClip cap) := by
  intro a b hab
  dsimp [reluClip]
  split_ifs <;> omega

/-- 活性化関数 `f` の区間伝播が健全（sound）であることの証明 -/
theorem monotone_activation_sound {f : Int → Int} (hf : MonotoneInt f)
    (iv : Interval) {x : Int} (hx : InInterval iv x) :
    f iv.lo ≤ f x ∧ f x ≤ f iv.hi := by
  exact ⟨hf hx.1, hf hx.2⟩

/-- 非負重み `w ≥ 0` の線形層に対する区間下界・上界伝播の健全性証明 -/
theorem nonneg_linear_sound {w b : Int} (hw : 0 ≤ w)
    (iv : Interval) {x : Int} (hx : InInterval iv x) :
    linearStep w b iv.lo ≤ linearStep w b x ∧
      linearStep w b x ≤ linearStep w b iv.hi := by
  dsimp [linearStep]
  have hlo : w * iv.lo ≤ w * x := mul_le_mul_of_nonneg_left hx.1 hw
  have hhi : w * x ≤ w * iv.hi := mul_le_mul_of_nonneg_left hx.2 hw
  exact ⟨by linarith, by linarith⟩

/-- 線形層＋単調活性化の合成ステップに対する出力安全性（下界・上界保証） -/
theorem layer_pipeline_sound {w b cap : Int}
    (hw : 0 ≤ w) (hcap : 0 ≤ cap)
    (iv : Interval) {x : Int} (hx : InInterval iv x) :
    let yLo := reluClip cap (linearStep w b iv.lo)
    let yHi := reluClip cap (linearStep w b iv.hi)
    let y   := reluClip cap (linearStep w b x)
    yLo ≤ y ∧ y ≤ yHi := by
  dsimp only
  have hlin := nonneg_linear_sound hw iv hx
  have hmon := reluClip_monotone hcap
  exact ⟨hmon hlin.1, hmon hlin.2⟩

end AIDiscreteVerification
