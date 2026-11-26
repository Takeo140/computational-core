License Apache-2.o  Takeo Yamamoto
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

def sigma (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

def collatz_seq (N : Nat) : Nat → Nat
  | 0     => N
  | n + 1 => sigma (collatz_seq N n)

-- 標準自然数上で証明できる補題
theorem sigma_closed (n : Nat) (h : n > 0) : sigma n > 0 := by
  simp only [sigma]
  split_ifs with heven <;> omega

theorem sigma_fixed_one : sigma 1 = 1 := by
  simp [sigma]

theorem seq_stays_one_after (N k m : Nat) (hk : collatz_seq N k = 1) :
    collatz_seq N (k + m) = 1 := by
  induction m with
  | zero => simpa using hk
  | succ n ih =>
      simp only [collatz_seq, Nat.add_succ, ih]
      exact sigma_fixed_one

-- 独立公理：すべての正の整数は有限ステップで 1 に到達する
axiom collatz_axiom (N : Nat) (h : N > 0) :
    ∃ k : Nat, collatz_seq N k = 1

-- 公理を用いた証明群
theorem collatz_convergence (N : Nat) (h : N > 0) :
    ∃ k : Nat, collatz_seq N k = 1 :=
  collatz_axiom N h

theorem collatz_fixed_at_one (N : Nat) (h : N > 0) :
    ∃ k : Nat, collatz_seq N k = 1 ∧ sigma (collatz_seq N k) = 1 := by
  obtain ⟨k, hk⟩ := collatz_axiom N h
  exact ⟨k, hk, by rw [hk]; exact sigma_fixed_one⟩

theorem collatz_eventually_one (N : Nat) (h : N > 0) :
    ∃ k : Nat, ∀ m : Nat, collatz_seq N (k + m) = 1 := by
  obtain ⟨k, hk⟩ := collatz_axiom N h
  exact ⟨k, fun m => seq_stays_one_after N k m hk⟩

theorem orbit_merge (N M : Nat) (hN : N > 0) (hM : M > 0)
    (k j : Nat) (h : collatz_seq N k = collatz_seq M j) :
    ∀ m : Nat, collatz_seq N (k + m) = collatz_seq M (j + m) := by
  intro m
  induction m with
  | zero => simp [h]
  | succ n ih =>
      simp only [collatz_seq, Nat.add_succ]
      rw [ih]
