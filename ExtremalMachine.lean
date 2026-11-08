/-!
# Extremal Machine, latest form — energy-based attractor dynamics

A single-file formal blueprint for a contemporary AI architecture,
fusing the two foundations of Takeo Yamamoto's formal-systems corpus:

* **F-Theory (the cosmology)** supplies the *extremal principle*:
  the world is organized by a functional whose extremum governs
  the dynamics.
* **computational-core** supplies the *convergence system* (収束系):
  every orbit is drawn to an attractor, as by a mathematical
  gravity.

The architecture here is the one shared by the current generation
of models — modern Hopfield networks (where attention *is* attractor
retrieval), energy-based models, diffusion samplers, and
free-energy world models:

* a pluggable **energy function** plays the role of the world model
  (in a deployed system this is the learned part);
* **inference is descent**: each step moves to the lowest-energy
  neighbour — computation as optimization, the extremal principle
  turned into dynamics;
* the machine **halts at an attractor**: a local minimum of the
  energy, where it rests.

## What is proved (no `sorry` anywhere)

Unlike a merely adopted convergence axiom, convergence here is
*derived*. For **any** energy function and **any** neighbourhood
structure on the natural-number state space:

* `step_energy_le`  — energy never increases along a step;
* `step_eq_or_lt`   — a step either rests or strictly descends;
* `step_eq_iff`     — the machine rests exactly at the local minima
                      of the energy (the attractors);
* `attractor_theorem` — from any starting state, the dynamics
                      reaches an attractor within `energy n` steps,
                      having never increased the energy.

For the concrete landscape whose energy is the distance to the
stored pattern `7` (a one-pattern memory):

* `localMin_seven`  — `7` is the *unique* attractor;
* `seven_reached`   — every orbit descends into `7`, in at most
                      `distTo 7 n` steps, machine-checked.

## Honest note

The energy function is the blueprint's interface to learning:
proving things about a *learned* energy is the taker's work.
What is proved here is the dynamics and its guarantees — descent,
termination, and the attractor characterization — for every
energy whatsoever. Q.E.D.

Author: Takeo Yamamoto (GitHub: Takeo140)
License: Apache-2.0
-/

set_option maxRecDepth 65536

namespace ExtremalMachine

/-! ## Running a dynamics -/

/-- Running a transition function `f` for `k` steps from `n`. -/
def iter (f : Nat → Nat) : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => iter f k (f n)

/-! ## The descent dynamics

One inference step: among the current state and its neighbours,
move to the one of least energy — steepest descent on the
energy landscape, resting when nothing is lower. -/

/-- Pick the lower-energy of two states; ties keep the incumbent. -/
def pick (energy : Nat → Nat) (best y : Nat) : Nat :=
  if energy y < energy best then y else best

/-- One descent step from `n`: fold the neighbourhood, keeping the
    least-energy state seen, starting from `n` itself. -/
def step (energy : Nat → Nat) (neighbors : Nat → List Nat) (n : Nat) : Nat :=
  (neighbors n).foldl (pick energy) n

theorem pick_cases (energy : Nat → Nat) (b y : Nat) :
    (pick energy b y = y ∧ energy y < energy b)
      ∨ (pick energy b y = b ∧ energy b ≤ energy y) := by
  unfold pick
  by_cases h : energy y < energy b
  · exact Or.inl ⟨ite_eq_left h, h⟩
  · exact Or.inr ⟨ite_eq_right h, by omega⟩

theorem pick_energy_le (energy : Nat → Nat) (b y : Nat) :
    energy (pick energy b y) ≤ energy b := by
  rcases pick_cases energy b y with ⟨hp, h⟩ | ⟨hp, -⟩
  · rw [hp]; exact Nat.le_of_lt h
  · rw [hp]; exact Nat.le_refl _

/-! ## Fold invariants: what one descent step guarantees -/

/-- Descent never raises the energy, over any fold. -/
theorem energy_foldl_le (energy : Nat → Nat) :
    ∀ (l : List Nat) (b : Nat),
      energy (l.foldl (pick energy) b) ≤ energy b := by
  intro l
  induction l with
  | nil => intro b; exact Nat.le_refl _
  | cons z zs ih =>
      intro b
      rw [List.foldl_cons]
      exact Nat.le_trans (ih (pick energy b z)) (pick_energy_le energy b z)

/-- The result of a fold is always the start or a listed state. -/
theorem foldl_mem (energy : Nat → Nat) :
    ∀ (l : List Nat) (b : Nat),
      l.foldl (pick energy) b ∈ b :: l := by
  intro l
  induction l with
  | nil => intro b; exact List.mem_cons_self
  | cons z zs ih =>
      intro b
      rw [List.foldl_cons]
      have hres := ih (pick energy b z)
      rcases pick_cases energy b z with ⟨hp, -⟩ | ⟨hp, -⟩
      · rw [hp] at hres ⊢
        exact List.mem_cons_of_mem b hres
      · rw [hp] at hres ⊢
        rw [List.mem_cons] at hres
        rcases hres with heq | hres
        · rw [heq]; exact List.mem_cons_self
        · exact List.mem_cons_of_mem b (List.mem_cons_of_mem z hres)

/-- The fold's result has energy at most that of any listed state:
    the fold really does find the minimum over what it scans. -/
theorem energy_foldl_le_of_mem (energy : Nat → Nat) :
    ∀ (l : List Nat) (b y : Nat), y ∈ l →
      energy (l.foldl (pick energy) b) ≤ energy y := by
  intro l
  induction l with
  | nil => intro b y hy; cases hy
  | cons z zs ih =>
      intro b y hy
      rw [List.foldl_cons]
      rw [List.mem_cons] at hy
      rcases hy with rfl | hy
      · rcases pick_cases energy b y with ⟨hp, -⟩ | ⟨hp, hle⟩
        · rw [hp]; exact energy_foldl_le energy zs y
        · rw [hp]; exact Nat.le_trans (energy_foldl_le energy zs b) hle
      · exact ih (pick energy b z) y hy

/-- If a fold moves away from its starting point, the energy has
    strictly dropped: movement is always paid for by descent. -/
theorem energy_foldl_lt_of_ne (energy : Nat → Nat) :
    ∀ (l : List Nat) (b : Nat), l.foldl (pick energy) b ≠ b →
      energy (l.foldl (pick energy) b) < energy b := by
  intro l
  induction l with
  | nil => intro b hne; exact absurd rfl hne
  | cons z zs ih =>
      intro b hne
      rw [List.foldl_cons] at hne ⊢
      rcases pick_cases energy b z with ⟨hp, hlt⟩ | ⟨hp, -⟩
      · have e1 := energy_foldl_le energy zs (pick energy b z)
        rw [hp] at e1 ⊢
        exact Nat.lt_of_le_of_lt e1 hlt
      · rw [hp] at hne ⊢
        exact ih b hne

/-- A fold starting at a state that is already minimal over the
    scanned list does not move. -/
theorem foldl_eq_self_of_min (energy : Nat → Nat) :
    ∀ (l : List Nat) (b : Nat), (∀ y ∈ l, energy b ≤ energy y) →
      l.foldl (pick energy) b = b := by
  intro l
  induction l with
  | nil => intro b _; rfl
  | cons z zs ih =>
      intro b hall
      rw [List.foldl_cons]
      have hp : pick energy b z = b := by
        have hge : energy b ≤ energy z := hall z List.mem_cons_self
        unfold pick
        exact ite_eq_right (by omega)
      rw [hp]
      exact ih b (fun y hy => hall y (List.mem_cons_of_mem z hy))

/-! ## Step guarantees -/

/-- One step never increases the energy. -/
theorem step_energy_le (energy : Nat → Nat) (neighbors : Nat → List Nat)
    (n : Nat) : energy (step energy neighbors n) ≤ energy n :=
  energy_foldl_le energy (neighbors n) n

/-- One step's energy is at most the energy of any neighbour. -/
theorem step_energy_le_of_mem (energy : Nat → Nat)
    (neighbors : Nat → List Nat) (n y : Nat) (hy : y ∈ neighbors n) :
    energy (step energy neighbors n) ≤ energy y :=
  energy_foldl_le_of_mem energy (neighbors n) n y hy

/-- A step either rests, or strictly descends. -/
theorem step_eq_or_lt (energy : Nat → Nat) (neighbors : Nat → List Nat)
    (n : Nat) :
    step energy neighbors n = n
      ∨ energy (step energy neighbors n) < energy n := by
  by_cases h : step energy neighbors n = n
  · exact Or.inl h
  · exact Or.inr (energy_foldl_lt_of_ne energy (neighbors n) n h)

/-- A local minimum of the energy: no neighbour is lower.
    These are the attractors of the dynamics. -/
def LocalMinimum (energy : Nat → Nat) (neighbors : Nat → List Nat)
    (x : Nat) : Prop :=
  ∀ y ∈ neighbors x, energy x ≤ energy y

/-- The machine rests exactly at the local minima:
    halting states and attractors are the same thing. -/
theorem step_eq_iff (energy : Nat → Nat) (neighbors : Nat → List Nat)
    (n : Nat) :
    step energy neighbors n = n ↔ LocalMinimum energy neighbors n := by
  constructor
  · intro h y hy
    have hle := step_energy_le_of_mem energy neighbors n y hy
    rwa [h] at hle
  · intro hall
    exact foldl_eq_self_of_min energy (neighbors n) n hall

/-- Energy along an orbit never exceeds the starting energy. -/
theorem energy_iter_le (energy : Nat → Nat) (neighbors : Nat → List Nat) :
    ∀ (k n : Nat),
      energy (iter (step energy neighbors) k n) ≤ energy n := by
  intro k
  induction k with
  | zero => intro n; exact Nat.le_refl _
  | succ k ih =>
      intro n
      exact Nat.le_trans (ih (step energy neighbors n))
        (step_energy_le energy neighbors n)

/-! ## The attractor theorem: convergence, derived -/

/-- From any state, descent reaches a resting state — an attractor —
    within `energy n` steps. Termination is not assumed; it is
    forced by strict descent on a natural-number energy. -/
theorem reaches_fixed (energy : Nat → Nat) (neighbors : Nat → List Nat) :
    ∀ (E n : Nat), energy n ≤ E →
      ∃ k, k ≤ energy n
        ∧ step energy neighbors (iter (step energy neighbors) k n)
            = iter (step energy neighbors) k n := by
  intro E
  induction E with
  | zero =>
      intro n hn
      have hE : energy n = 0 := by omega
      have hs : step energy neighbors n = n := by
        rcases step_eq_or_lt energy neighbors n with h | h
        · exact h
        · rw [hE] at h; exact absurd h (Nat.not_lt_zero _)
      exact ⟨0, by omega, hs⟩
  | succ E ih =>
      intro n hn
      by_cases hs : step energy neighbors n = n
      · exact ⟨0, by omega, hs⟩
      · have hlt : energy (step energy neighbors n) < energy n :=
          (step_eq_or_lt energy neighbors n).resolve_left hs
        have hle : energy (step energy neighbors n) ≤ E := by omega
        obtain ⟨k, hk, hfix⟩ := ih (step energy neighbors n) hle
        exact ⟨k + 1, by omega, hfix⟩

/-- The blueprint's coherence theorem, latest form:
    from every starting state, the dynamics descends to an
    attractor — a local extremum of the energy — in finitely
    many steps, and the energy there is no more than at the start.
    Principles in (an energy, a neighbourhood); theorems out. -/
theorem attractor_theorem (energy : Nat → Nat) (neighbors : Nat → List Nat)
    (n : Nat) :
    ∃ k x, x = iter (step energy neighbors) k n ∧ k ≤ energy n
      ∧ LocalMinimum energy neighbors x ∧ energy x ≤ energy n := by
  obtain ⟨k, hk, hfix⟩ := reaches_fixed energy neighbors (energy n) n
    (Nat.le_refl _)
  exact ⟨k, iter (step energy neighbors) k n, rfl, hk,
    (step_eq_iff energy neighbors _).mp hfix,
    energy_iter_le energy neighbors k n⟩

/-! ## A concrete memory: one stored pattern -/

/-- Distance between two states (the energy of a one-pattern
    memory landscape). -/
def distTo (t n : Nat) : Nat :=
  if n ≥ t then n - t else t - n

/-- The landscape of a memory holding the single pattern `7`. -/
def energy7 (n : Nat) : Nat := distTo 7 n

/-- Neighbourhood: one step down or up the state line. -/
def neighbors7 (n : Nat) : List Nat := [n - 1, n + 1]

/-- The descent dynamics on this landscape. -/
def step7 (n : Nat) : Nat := step energy7 neighbors7 n

/-- The stored pattern is the unique attractor of its landscape. -/
theorem localMin_seven (n : Nat) :
    LocalMinimum energy7 neighbors7 n ↔ n = 7 := by
  constructor
  · intro h
    by_cases hn : n = 7
    · exact hn
    · rcases Nat.lt_or_gt_of_ne hn with hlt | hgt
      · have hle := h (n + 1) (by simp [neighbors7])
        have e1 : energy7 n = 7 - n := by
          unfold energy7 distTo
          exact ite_eq_right (by omega)
        have e2 : energy7 (n + 1) = 7 - (n + 1) := by
          unfold energy7 distTo
          by_cases h7 : n + 1 ≥ 7
          · rw [ite_eq_left h7]; omega
          · exact ite_eq_right h7
        omega
      · have hle := h (n - 1) (by simp [neighbors7])
        have e1 : energy7 n = n - 7 := by
          unfold energy7 distTo
          exact ite_eq_left (by omega)
        have e2 : energy7 (n - 1) = (n - 1) - 7 := by
          unfold energy7 distTo
          exact ite_eq_left (by omega)
        omega
  · rintro rfl
    intro y hy
    simp [neighbors7] at hy
    rcases hy with rfl | rfl <;> decide

/-- Every orbit of the concrete dynamics descends into the stored
    pattern — the attractor — within `distTo 7 n` steps. -/
theorem seven_reached (n : Nat) :
    ∃ k, k ≤ energy7 n ∧ iter step7 k n = 7 := by
  obtain ⟨k, x, hx, hk, hmin, -⟩ := attractor_theorem energy7 neighbors7 n
  have hx7 : x = 7 := (localMin_seven x).mp hmin
  exact ⟨k, hk, hx.symm.trans hx7⟩

/-- Descent in action, machine-checked: 12 walks down to the pattern. -/
example : iter step7 5 12 = 7 := by decide

/-- And 4 climbs up to it. -/
example : iter step7 3 4 = 7 := by decide

/-- The attractor rests. -/
example : step7 7 = 7 := by decide

end ExtremalMachine

/-! ## Axiom check

The theorems must depend only on the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`) — no `sorryAx`,
and no adopted convergence axiom: convergence is derived. -/

#print axioms ExtremalMachine.attractor_theorem
#print axioms ExtremalMachine.step_eq_iff
#print axioms ExtremalMachine.seven_reached
#print axioms ExtremalMachine.localMin_seven
