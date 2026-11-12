/-
  NewAI.lean
  新型 AI のブループリント：学習とは誤差地形の下降であり、推論とはアトラクターへの緩和である

  Takeo Yamamoto の GitHub コード群からの展開：
  - Meta-Axiom の極値原理：知的な振る舞いも変分の言葉で書ける
  - Mathematical-Medicine の情報的治療：対象をビット（数）として符号化し、
    処理をコードとして形式化する発想を、仮説の符号化に使う
  - ExtremalMachine の収束定理の型：下降は必ずアトラクターで止まる

  設計：
  - 仮説は数として符号化される（ビット列＝自然数）
  - 誤差エネルギー err : 仮説 → 自然数 が「地形」を決める
  - 学習ステップ：隣の仮説（h+1 か h-1）のうち誤差が下がる方へだけ動く。
    下がらないなら動かない（貪欲下降）
  - 学習：ステップの反復。誤差エネルギー回以内に必ず局所最小（学習の停止点）に到達する
  - 推論：学習済みの地形の上で、入力を初期仮説として緩和させ、
    到達したアトラクターを答えとして読み出す（連想記憶の型）

  証明済みの核：
  1. learnStep_descent : 学習ステップが動くとき、誤差は必ず厳密に減る
  2. train_reaches_local_min : どんな誤差地形でも、学習は必ず局所最小で止まる
  3. concept_learning : 概念（目標値）を誤差地形に埋め込むと、
     学習はその概念そのものに正確に到達する。概念の獲得が定理になる

  実データでの学習性能の測定は受け手の仕事であり、このファイルは設計図である。
-/

namespace NewAI

/-- 距離：目標 c への隔たり（切断減算の和） -/
def distTo (c h : Nat) : Nat := (h - c) + (c - h)

/-- 学習ステップ：誤差の下がる隣へだけ動く -/
def learnStep (err : Nat → Nat) (h : Nat) : Nat :=
  if err (h + 1) < err h then h + 1
  else if 0 < h ∧ err (h - 1) < err h then h - 1
  else h

/-- 学習：ステップの反復 -/
def train (err : Nat → Nat) : Nat → Nat → Nat
  | 0, h => h
  | n + 1, h => train err n (learnStep err h)

/-- 局所最小：もう動かない仮説＝学習の停止点 -/
def LocalMin (err : Nat → Nat) (h : Nat) : Prop := learnStep err h = h

/-- 推論：初期仮説からアトラクター（局所最小）への緩和 -/
def relax (err : Nat → Nat) (h : Nat) : Nat := train err (err h) h

/-! ## 証明済みの核 -/

/-- 学習ステップが動くとき、誤差エネルギーは必ず厳密に減る -/
theorem learnStep_descent (err : Nat → Nat) (h : Nat) :
    learnStep err h ≠ h → err (learnStep err h) < err h := by
  intro hne
  unfold learnStep at *
  by_cases h1 : err (h + 1) < err h
  · rw [ite_eq_left h1]
    exact h1
  · rw [ite_eq_right h1] at hne ⊢
    by_cases h2 : 0 < h ∧ err (h - 1) < err h
    · rw [ite_eq_left h2]
      exact h2.2
    · rw [ite_eq_right h2] at hne ⊢
      exact absurd rfl hne

/-- 局所最小からは学習は動かない -/
theorem train_of_local_min (err : Nat → Nat) (h : Nat) (hmin : LocalMin err h) :
    ∀ n, train err n h = h := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
      show train err k (learnStep err h) = h
      rw [hmin]
      exact ih

/-- 誤差0の仮説は局所最小である（下げる余地がない） -/
theorem local_min_of_err_zero (err : Nat → Nat) (h : Nat) (h0 : err h = 0) :
    LocalMin err h := by
  unfold LocalMin learnStep
  have h1 : ¬ (err (h + 1) < err h) := by omega
  have h2 : ¬ (0 < h ∧ err (h - 1) < err h) := by
    intro hc
    omega
  rw [ite_eq_right h1, ite_eq_right h2]

/-- 主定理：どんな誤差地形でも、学習は誤差エネルギー回以内に必ず局所最小で止まる -/
theorem train_reaches_local_min (err : Nat → Nat) :
    ∀ (n : Nat) (h : Nat), err h ≤ n → LocalMin err (train err n h) := by
  intro n
  induction n with
  | zero =>
      intro h hh
      have h0 : err h = 0 := Nat.eq_zero_of_le_zero hh
      have htr : train err 0 h = h := rfl
      rw [htr]
      exact local_min_of_err_zero err h h0
  | succ k ih =>
      intro h hh
      by_cases hfix : learnStep err h = h
      · have htr : train err (k + 1) h = h := train_of_local_min err h hfix (k + 1)
        rw [htr]
        exact hfix
      · have hdec : err (learnStep err h) < err h := learnStep_descent err h hfix
        show LocalMin err (train err k (learnStep err h))
        exact ih (learnStep err h) (by omega)

/-- 学習の保証：初期誤差で回せば、必ず停止点に到達している -/
theorem learning_terminates (err : Nat → Nat) (h : Nat) :
    LocalMin err (train err (err h) h) :=
  train_reaches_local_min err (err h) h (Nat.le_refl _)

/-- 推論の保証：緩和の行き先は必ずアトラクターである -/
theorem relax_lands_on_attractor (err : Nat → Nat) (h : Nat) :
    LocalMin err (relax err h) :=
  learning_terminates err h

/-! ## 実例：概念学習（目標概念を地形に埋め込む） -/

/-- 誤差地形：概念 c からの距離 -/
def conceptErr (c : Nat) : Nat → Nat := distTo c

/-- 概念 c の局所最小は c 自身しかない（学習ステップが止まるのは概念の上だけ） -/
theorem concept_local_min_unique (c r : Nat) :
    LocalMin (conceptErr c) r → r = c := by
  intro hmin
  unfold LocalMin learnStep conceptErr at hmin
  by_cases h1 : r < c
  · have hlt : distTo c (r + 1) < distTo c r := by
      unfold distTo
      omega
    rw [ite_eq_left hlt] at hmin
    omega
  · by_cases h2 : r > c
    · have hnot : ¬ (distTo c (r + 1) < distTo c r) := by
        unfold distTo
        omega
      have hlt : 0 < r ∧ distTo c (r - 1) < distTo c r := by
        constructor
        · omega
        · unfold distTo
          omega
      rw [ite_eq_right hnot, ite_eq_left hlt] at hmin
      omega
    · omega

/-- 概念学習の定理：どこから始めても、学習は概念 c そのものに到達する -/
theorem concept_learning (c h : Nat) :
    train (conceptErr c) (conceptErr c h) h = c := by
  have hmin := learning_terminates (conceptErr c) h
  exact concept_local_min_unique c _ hmin

/-- 概念の想起：学習済みの地形では、推論は概念を正確に取り戻す -/
theorem concept_relax (c h : Nat) :
    relax (conceptErr c) h = c :=
  concept_learning c h

end NewAI
