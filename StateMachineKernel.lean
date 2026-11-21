License Apache-2.0  Takeo Yamamoto
import Mathlib.Data.Nat.Basic

namespace StateMachineKernel

/-- システムの状態：単調増加する世代番号 `seq` と累積メトリクス `total` -/
structure State where
  seq : Nat
  total : Nat
  deriving DecidableEq, Repr

/-- 入力イベント：デルタ値 `delta` -/
structure Event where
  delta : Nat
  deriving DecidableEq, Repr

/-- 状態遷移カーネル：イベントを適用し、世代を1進めて累積値を更新する -/
def step (s : State) (ev : Event) : State :=
  { seq := s.seq + 1
    total := s.total + ev.delta }

/-- 不変量：累積値は常に初期値 `initTotal` 以上である -/
def inv (initTotal : Nat) (s : State) : Prop :=
  initTotal ≤ s.total

/-- 1ステップの遷移でシーケンス番号は必ず厳密に増加する -/
theorem step_seq_lt (s : State) (ev : Event) :
    s.seq < (step s ev).seq := by
  simp [step]

/-- 不変量 `initTotal ≤ s.total` は任意のイベント適用で保存される -/
theorem step_preserves_inv {initTotal : Nat} {s : State} (ev : Event)
    (h : inv initTotal s) :
    inv initTotal (step s ev) := by
  dsimp [inv, step] at h ⊢
  omega

/-- 複数イベントの畳み込み（バッチ処理）でも不変量が保存される -/
theorem foldl_preserves_inv {initTotal : Nat} (evs : List Event) {s : State}
    (h : inv initTotal s) :
    inv initTotal (evs.foldl step s) := by
  induction evs generalizing s with
  | nil =>
    simpa using h
  | cons ev rest ih =>
    simpa [List.foldl] using ih (step_preserves_inv ev h)

end StateMachineKernel
