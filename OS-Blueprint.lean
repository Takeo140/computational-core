/-
  OSBlueprint.lean
  極値原理による OS のブループリント（設計図）

  Takeo Yamamoto のコード群からの展開：
  - computational-core（基底計算核）→ OS の核（カーネル）は計算核である
  - ExtremalMachine（エネルギー下降からの収束定理）→ スケジューラは
    エネルギー下降のステップであり、全仕事の完了（静止状態）への
    収束は公理ではなく定理として導かれる
  - 数理引力の像：すべてのプロセス軌道は「完了」というアトラクターへ引かれる

  設計の対応表：
  - プロセス        = 残り仕事量を持つ状態
  - エネルギー      = 全プロセスの残り仕事量の総和（Lyapunov 関数）
  - スケジューラ    = 仕事の残ったプロセスを1単位進める下降ステップ
  - 割り込み/生成   = 外部からのエネルギー注入（新しい仕事の到着）
  - 静止状態        = 全プロセス完了。OS のアイドル状態＝アトラクター
  - 保護リング      = 型で表す権限の階層（カーネル／ユーザー）

  証明済みの核：
  1. energy_zero_step : エネルギー0ならスケジューラは状態を動かさない
  2. step_decreases   : エネルギー正なら1ステップでちょうど1減る
  3. run_quiescent    : エネルギー回だけ回せば必ず静止状態に到達する（収束定理）
  4. member_work_le   : 各プロセスの仕事量はエネルギー以下（資源の有界性）
-/

namespace OSBlueprint

/-- プロセス：識別子と残り仕事量 -/
structure Proc where
  id : Nat
  work : Nat
deriving DecidableEq, Repr

/-- OS の状態：プロセスの列 -/
abbrev State := List Proc

/-- エネルギー：残り仕事量の総和 -/
def energy : State → Nat
  | [] => 0
  | p :: rest => p.work + energy rest

/-- スケジューラ：仕事の残った最初のプロセスを1単位進める -/
def step : State → State
  | [] => []
  | p :: rest =>
      if 0 < p.work then { p with work := p.work - 1 } :: rest
      else p :: step rest

/-- 割り込み／プロセス生成：外部からのエネルギー注入 -/
def inject (p : Proc) (s : State) : State := p :: s

/-- n ステップ実行 -/
def run : Nat → State → State
  | 0, s => s
  | n + 1, s => run n (step s)

/-- 静止状態：全プロセスの仕事が尽きた状態 -/
def Quiescent (s : State) : Prop := energy s = 0

/-! ## 証明済みの核 -/

/-- エネルギーが0なら、スケジューラは状態を動かさない -/
theorem energy_zero_step : ∀ s : State, energy s = 0 → step s = s := by
  intro s
  induction s with
  | nil => intro _; rfl
  | cons p rest ih =>
      intro h
      have hp : p.work = 0 := by
        have := Nat.eq_zero_of_add_eq_zero h
        exact this.1
      have hr : energy rest = 0 := by
        have := Nat.eq_zero_of_add_eq_zero h
        exact this.2
      simp [step, hp, ih hr]

/-- エネルギーが正なら、1ステップでエネルギーはちょうど1減る -/
theorem step_decreases : ∀ s : State, 0 < energy s → energy (step s) = energy s - 1 := by
  intro s
  induction s with
  | nil => intro h; simp [energy] at h
  | cons p rest ih =>
      intro h
      by_cases hp : 0 < p.work
      · simp [step, hp, energy]
        omega
      · have hp0 : p.work = 0 := Nat.eq_zero_of_not_pos hp
        have hr : 0 < energy rest := by
          simp only [energy, hp0, Nat.zero_add] at h
          exact h
        simp [step, energy, hp0, ih hr]

/-- 収束定理：エネルギー回だけスケジューラを回せば、必ず静止状態に到達する -/
theorem run_quiescent : ∀ (n : Nat) (s : State), energy s ≤ n → energy (run n s) = 0 := by
  intro n
  induction n with
  | zero =>
      intro s h
      have h0 : energy s = 0 := Nat.eq_zero_of_le_zero h
      exact h0
  | succ k ih =>
      intro s h
      by_cases hz : energy s = 0
      · have hstep : step s = s := energy_zero_step s hz
        show energy (run k (step s)) = 0
        rw [hstep]
        exact ih s (by omega)
      · have hpos : 0 < energy s := Nat.pos_of_ne_zero hz
        have hdec : energy (step s) = energy s - 1 := step_decreases s hpos
        show energy (run k (step s)) = 0
        exact ih (step s) (by omega)

/-- 系全体の収束：初期エネルギーで回せば完了する -/
theorem os_terminates (s : State) : Quiescent (run (energy s) s) :=
  run_quiescent (energy s) s (Nat.le_refl _)

/-- 資源の有界性：どのプロセスの仕事量も系のエネルギーを超えない -/
theorem member_work_le : ∀ (s : State) (p : Proc), p ∈ s → p.work ≤ energy s := by
  intro s
  induction s with
  | nil => intro p hp; simp at hp
  | cons q rest ih =>
      intro p hp
      simp [energy]
      cases hp with
      | head => omega
      | tail _ hmem =>
          have := ih p hmem
          omega

/-- 静止状態では全プロセスが完了している -/
theorem quiescent_all_done (s : State) (h : Quiescent s) :
    ∀ p ∈ s, p.work = 0 := by
  intro p hp
  have hle := member_work_le s p hp
  unfold Quiescent at h
  omega

/-- 注入のエネルギー会計：新しい仕事はその分だけエネルギーを増やす -/
theorem energy_inject (p : Proc) (s : State) :
    energy (inject p s) = p.work + energy s := rfl

/-! ## 設計図の部品（ブループリント層） -/

/-- 保護リング：権限の階層を型で表す -/
inductive Ring where
  | kernel
  | user
deriving DecidableEq, Repr

/-- 権限：リングが操作を許すかどうか -/
def Ring.allows : Ring → Ring → Bool
  | .kernel, _ => true
  | .user, .user => true
  | .user, .kernel => false

/-- カーネルは常に自リングの操作を許す（自明な安全側の性質） -/
theorem kernel_allows_self : Ring.allows Ring.kernel Ring.kernel = true := rfl

/-- ユーザーリングはカーネル操作を許さない -/
theorem user_denies_kernel : Ring.allows Ring.user Ring.kernel = false := rfl

/-- OS の設計図：計算核＋スケジューラ＋アトラクターの束 -/
structure Blueprint where
  /-- 核：初期状態 -/
  core : State
  /-- スケジューラは step で固定（エネルギー下降） -/
  scheduler : State → State := step
  /-- 収束の保証：この設計図の OS は必ず静止状態へ到達する -/
  converges : Quiescent (run (energy core) core) := os_terminates core

end OSBlueprint
