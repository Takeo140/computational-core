/-
  NewComputer.lean
  新型コンピュータのブループリント：エネルギー地形がプログラムである計算機

  Takeo Yamamoto の GitHub コード群（Takeo140）からの展開：
  - computational-core（基底計算核）と ExtremalMachine（エネルギー下降からの
    収束定理）の原理を一般化する。計算とは、エネルギー地形の上を
    厳密に下降し、アトラクター（不動点）に到達することである。
  - 従来機（Turing/Neumann 型）が「命令列」をプログラムとするのに対し、
    この計算機は「地形（エネルギー関数）」をプログラムとする。
    地形を置けば、下降の仕組みが計算を実行し、答えはアトラクターとして現れる。

  証明済みの核：
  1. any_landscape_terminates : どんな地形と下降ステップの組でも、
     エネルギー回以内の反復で必ず不動点（アトラクター）に到達する。
     終わらない計算は、この設計図の中には存在しない。
  2. countdown / target  : 具体的な地形の実例（数え下げ／目標探索）。
  3. product             : 2つの計算機は合成できる（エネルギーは和になる）。
     計算機の部品化＝設計図の積み上げが可能であることの保証。

  なお実機の構築と性能の測定は受け手の仕事であり、このファイルは設計図である。
-/

namespace NewComputer

/-- 下降機械：エネルギー地形と、動くときは必ずエネルギーを下げるステップ。
    この2つ組が、この計算機における「プログラム」の形である。 -/
structure DescentMachine (σ : Type) where
  energy : σ → Nat
  step : σ → σ
  descent : ∀ s, step s ≠ s → energy (step s) < energy s

namespace DescentMachine

/-- 反復実行 -/
def run {σ : Type} (M : DescentMachine σ) : Nat → σ → σ
  | 0, s => s
  | n + 1, s => M.run n (M.step s)

/-- エネルギー0の状態は不動点である（下げる余地がない） -/
theorem fixed_of_energy_zero {σ : Type} (M : DescentMachine σ) (s : σ)
    (h : M.energy s = 0) : M.step s = s := by
  by_cases hfix : M.step s = s
  · exact hfix
  · have hlt := M.descent s hfix
    exact False.elim (by omega)

/-- 不動点からはもう動かない -/
theorem run_of_fixed {σ : Type} (M : DescentMachine σ) (s : σ) (h : M.step s = s) :
    ∀ n, M.run n s = s := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
      show M.run k (M.step s) = s
      rw [h]
      exact ih

/-- 主定理：どんな地形でも、エネルギー回以内の反復でアトラクターに到達する -/
theorem any_landscape_terminates {σ : Type} (M : DescentMachine σ) :
    ∀ (n : Nat) (s : σ), M.energy s ≤ n → M.step (M.run n s) = M.run n s := by
  intro n
  induction n with
  | zero =>
      intro s h
      have h0 : M.energy s = 0 := Nat.eq_zero_of_le_zero h
      exact fixed_of_energy_zero M s h0
  | succ k ih =>
      intro s h
      by_cases hfix : M.step s = s
      · have hrun : M.run (k + 1) s = s := run_of_fixed M s hfix (k + 1)
        rw [hrun]
        exact hfix
      · have hlt : M.energy (M.step s) < M.energy s := M.descent s hfix
        show M.step (M.run k (M.step s)) = M.run k (M.step s)
        exact ih (M.step s) (by omega)

/-- 系全体の保証：初期エネルギーで回せば答え（アトラクター）が得られる -/
theorem computes {σ : Type} (M : DescentMachine σ) (s : σ) :
    M.step (M.run (M.energy s) s) = M.run (M.energy s) s :=
  any_landscape_terminates M (M.energy s) s (Nat.le_refl _)

end DescentMachine

/-! ## 実例1：数え下げ機械（地形は恒等、アトラクターは0） -/

/-- エネルギー＝状態そのもの。ステップは1減らす。 -/
def countdown : DescentMachine Nat where
  energy := fun s => s
  step := fun s => s - 1
  descent := by
    intro s h
    have hs : s - 1 ≠ s := h
    show s - 1 < s
    omega

/-- 数え下げ機械は必ず0に到達する -/
theorem countdown_computes (s : Nat) :
    countdown.run (countdown.energy s) s = 0 := by
  have hfix := DescentMachine.computes countdown s
  have h1 : countdown.step (countdown.run (countdown.energy s) s)
      = (countdown.run (countdown.energy s) s) - 1 := rfl
  by_cases h0 : countdown.run (countdown.energy s) s = 0
  · exact h0
  · have hpos : 0 < countdown.run (countdown.energy s) s := Nat.pos_of_ne_zero h0
    omega

/-! ## 実例2：目標探索機械（地形は目標までの距離、アトラクターは目標） -/

/-- 目標 t への距離（切断減算の和で表す） -/
def distTo (t s : Nat) : Nat := (s - t) + (t - s)

/-- 目標へ1歩近づく -/
def towardStep (t s : Nat) : Nat :=
  if s < t then s + 1 else if s > t then s - 1 else s

/-- 目標探索機械 -/
def targetMachine (t : Nat) : DescentMachine Nat where
  energy := distTo t
  step := towardStep t
  descent := by
    intro s h
    show distTo t (towardStep t s) < distTo t s
    unfold towardStep distTo
    by_cases h1 : s < t
    · rw [ite_eq_left h1]
      omega
    · by_cases h2 : s > t
      · rw [ite_eq_right h1, ite_eq_left h2]
        omega
      · exfalso
        exact h (by unfold towardStep; rw [ite_eq_right h1, ite_eq_right h2])

/-- 目標探索機械のアトラクターは目標そのものである -/
theorem target_is_attractor (t s : Nat) :
    (targetMachine t).run ((targetMachine t).energy s) s = t := by
  have hfix := DescentMachine.computes (targetMachine t) s
  have hstep : towardStep t ((targetMachine t).run ((targetMachine t).energy s) s)
      = (targetMachine t).run ((targetMachine t).energy s) s := hfix
  unfold towardStep at hstep
  by_cases h1 : (targetMachine t).run ((targetMachine t).energy s) s < t
  · simp only [h1, ite_true] at hstep
    omega
  · by_cases h2 : (targetMachine t).run ((targetMachine t).energy s) s > t
    · simp only [h1, ite_false, h2, ite_true] at hstep
      omega
    · omega

/-! ## 合成：2つの下降機械は1つの下降機械になる -/

/-- 直積機械：左が動くうちは左を進め、左が止まったら右を進める。
    エネルギーは2つのエネルギーの和。 -/
def product {σ τ : Type} [DecidableEq σ] (M1 : DescentMachine σ) (M2 : DescentMachine τ) :
    DescentMachine (σ × τ) where
  energy := fun p => M1.energy p.1 + M2.energy p.2
  step := fun p => if M1.step p.1 ≠ p.1 then (M1.step p.1, p.2) else (p.1, M2.step p.2)
  descent := by
    intro p h
    by_cases h1 : M1.step p.1 = p.1
    · have hne : ¬ (M1.step p.1 ≠ p.1) := fun hd => hd h1
      by_cases h2 : M2.step p.2 = p.2
      · exfalso
        apply h
        show (if M1.step p.1 ≠ p.1 then (M1.step p.1, p.2) else (p.1, M2.step p.2)) = p
        rw [ite_eq_right hne, h2]
      · have hd := M2.descent p.2 h2
        rw [ite_eq_right hne]
        show M1.energy p.1 + M2.energy (M2.step p.2) < M1.energy p.1 + M2.energy p.2
        omega
    · have hd := M1.descent p.1 h1
      rw [ite_eq_left h1]
      show M1.energy (M1.step p.1) + M2.energy p.2 < M1.energy p.1 + M2.energy p.2
      omega

end NewComputer
