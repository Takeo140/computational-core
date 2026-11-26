-- License Apache-2.0  Takeo Yamamoto
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

def sigma (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

def collatz_seq (N : Nat) : Nat → Nat
  | 0     => N
  | n + 1 => sigma (collatz_seq N n)

-- 標準的な公理系（ZFC相当の標準基礎公理）上で証明できる補題・定理
theorem sigma_closed (n : Nat) (h : n > 0) : sigma n > 0 := by
  simp only [sigma]
  split_ifs with heven <;> omega

theorem sigma_fixed_one : sigma 1 = 1 := by
  simp [sigma]

theorem sigma_even_decrease (n : Nat) (h : n > 0) (heven : n % 2 = 0) :
    sigma n < n ∧ n - sigma n = n / 2 := by
  simp only [sigma, heven, ↓reduceIte]
  omega

theorem sigma_odd_increase (n : Nat) (hodd : n % 2 = 1) :
    sigma n > n ∧ sigma n - n = 2 * n + 1 := by
  have hne : ¬ (n % 2 = 0) := by omega
  simp only [sigma, hne, ↓reduceIte]
  omega

theorem sigma_odd_then_even_step (n : Nat) (hodd : n % 2 = 1) :
    sigma (sigma n) = (3 * n + 1) / 2 := by
  have hne : ¬ (n % 2 = 0) := by omega
  have heven2 : (3 * n + 1) % 2 = 0 := by omega
  simp only [sigma, hne, heven2, ↓reduceIte]

theorem seq_stays_one_after (N k m : Nat) (hk : collatz_seq N k = 1) :
    collatz_seq N (k + m) = 1 := by
  induction m with
  | zero => simpa using hk
  | succ n ih =>
      simp only [collatz_seq, Nat.add_succ, ih]
      exact sigma_fixed_one

theorem orbit_merge (N M : Nat) (hN : N > 0) (hM : M > 0)
    (k j : Nat) (h : collatz_seq N k = collatz_seq M j) :
    ∀ m : Nat, collatz_seq N (k + m) = collatz_seq M (j + m) := by
  intro m
  induction m with
  | zero => simp [h]
  | succ n ih =>
      simp only [collatz_seq, Nat.add_succ]
      rw [ih]
