/-
  Unified Physical AI Macro-Kernel (ACM-TY × F-Theory × UHA)
  License: Apache 2.0
  Author: Takeo Yamamoto
-/

import Mathlib

namespace UnifiedPhysicalAI

/-!
============================================================
1. UHA (UltraCore HyperAlgebra) & 64-bit Word Core
============================================================
-/

/-- 64-bit Modular Word Type for Branchless UHA Computations -/
abbrev Word := ZMod (2 ^ 64)

namespace Word

def zero : Word := 0
def one  : Word := 1

/-- 非線形 UHA 遷移マップ（LCGベース・情報ロスなし） -/
def uhaStep (state : Word) (action : Word) (disturbance : Word) : Word :=
  state * 6364136223846793005 + action * 1442695040888963407 + disturbance + 1

/-- 分岐なしセレクト -/
def select (c a b : Word) : Word := c * a + (1 - c) * b

theorem select_one (a b : Word) : select 1 a b = a := by simp [select]
theorem select_zero (a b : Word) : select 0 a b = b := by simp [select]

theorem isUnit_natCast_of_odd (m : Nat) (hm : m % 2 = 1) :
    IsUnit ((m : Nat) : ZMod (2 ^ 64)) := by
  rw [ZMod.isUnit_iff_coprime]
  have h2 : Nat.Coprime 2 m :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)
  exact (Nat.Coprime.pow_left 64 h2).symm

theorem stateConst_isUnit : IsUnit (6364136223846793005 : Word) := by
  have h := isUnit_natCast_of_odd 6364136223846793005 (by norm_num)
  simpa using h

theorem actionConst_isUnit : IsUnit (1442695040888963407 : Word) := by
  have h := isUnit_natCast_of_odd 1442695040888963407 (by norm_num)
  simpa using h

theorem cancel_right {u a b : Word} (hu : IsUnit u) (h : a * u = b * u) : a = b :=
  hu.mul_right_cancel h

theorem uhaStep_injective_state (a d : Word) :
    Function.Injective (fun s : Word => uhaStep s a d) := by
  intro s t h
  simp only [uhaStep] at h
  have h' : s * 6364136223846793005 = t * 6364136223846793005 := by
    linear_combination h
  exact cancel_right stateConst_isUnit h'

end Word

/-!
============================================================
2. F-Theory Core (Extremization Principle δF = 0)
============================================================
-/

structure FState where
  stateVal : Word
  energy   : Word
  entropy  : Word

def FState.evaluateF (s : FState) : Word :=
  s.energy - s.entropy

def FState.isExtremal (s : FState) (threshold : Word) : Bool :=
  decide (ZMod.val s.evaluateF < ZMod.val threshold)

def FState.deltaF (s s' : FState) : Word :=
  s'.evaluateF - s.evaluateF

def FState.IsStationary (s s' : FState) : Prop :=
  s.deltaF s' = 0

theorem FState.deltaF_self (s : FState) : s.deltaF s = 0 := by
  simp [FState.deltaF]

theorem FState.isStationary_iff (s s' : FState) :
    s.IsStationary s' ↔ s'.evaluateF = s.evaluateF := by
  unfold FState.IsStationary FState.deltaF
  exact sub_eq_zero

/-!
============================================================
3. ACM-TY: Multilayer Computation Core (UHA tensor × BSCM × DIFD)
============================================================
-/

namespace ACMTY

structure UHA (n : Nat) where
  coords : Fin n → Word

namespace UHA

variable {n : Nat}

def zero : UHA n := ⟨fun _ => 0⟩

def add (x y : UHA n) : UHA n :=
  ⟨fun i => x.coords i + y.coords i⟩

instance : Add (UHA n) := ⟨add⟩

def smul (a : Word) (x : UHA n) : UHA n :=
  ⟨fun i => a * x.coords i⟩

instance : SMul Word (UHA n) := ⟨smul⟩

def norm (x : UHA n) : Word :=
  ∑ i : Fin n, (x.coords i) * (x.coords i)

theorem norm_zero : norm (zero : UHA n) = 0 := by
  simp [norm, zero]

end UHA

/-! BSCM (Discrete Control Core) -/
namespace BSCM

def delta (s : Word) : Word :=
  let v := s.val
  if v % 2 = 0 then ((v / 2 : Nat) : Word) else (((v + 1) / 2 : Nat) : Word)

def controlStep (current_state external_input : Word) : Word :=
  delta (current_state + external_input)

def entropy (s : Word) : Word :=
  let v := s.val
  ((v % 256 + (v / 256) % 256 : Nat) : Word)

end BSCM

/-! GIFE & DIFD (Field & Fluid Dynamics) -/

structure Entity (n : Nat) where
  id       : Nat
  state    : UHA n
  fState   : FState
  genome   : Word
  discrete : Word

structure Topology (n : Nat) where
  connMatrix : Fin n → Fin n → Word
  viscosity  : Word
  curvature  : Word

namespace Topology

variable {n : Nat}
def conn (top : Topology n) (i j : Fin n) : Word := top.connMatrix i j

end Topology

structure FieldState (n : Nat) where
  entities : List (Entity n)
  entropy  : Word
  topology : Topology n

def idx? (n k : Nat) : Option (Fin n) :=
  if h : k % n < n then some ⟨k % n, h⟩ else none

def connAt {n : Nat} (top : Topology n) (a b : Nat) : Word :=
  match idx? n a, idx? n b with
  | some i, some j => top.conn i j
  | _, _ => 0

namespace DIFD

variable {n : Nat}

def clipViscosity (v : Word) : Word :=
  if v.val > 1000000 then (1000000 : Word) else v

def decayVortex (c : Word) : Word :=
  ((c.val / 2 : Nat) : Word)

def normalizePressure (p : Word) : Word :=
  if p.val > 10 ^ 12 then ((10 ^ 12 : Nat) : Word) else p

def cfl (vel : UHA n) (visc : Word) : Bool :=
  decide (vel.norm.val < (visc * visc).val)

def diffuse (top : Topology n) (e : Entity n) (neighbors : List (Entity n)) : UHA n :=
  let total : UHA n :=
    neighbors.foldl
      (fun acc nb => UHA.add acc (UHA.smul (connAt top e.id nb.id) nb.state))
      UHA.zero
  let w : Word :=
    neighbors.foldl (fun a nb => a + connAt top e.id nb.id) 0
  if w = 0 then e.state else UHA.smul w⁻¹ total

def fluidUpdate (top : Topology n) (entropy : Word) (e : Entity n)
    (neighbors : List (Entity n)) : UHA n :=
  let visc := clipViscosity top.viscosity
  let d    := diffuse top e neighbors
  let v    := UHA.smul (decayVortex top.curvature) e.state
  let p    := UHA.smul (normalizePressure entropy) e.state
  if cfl d visc then UHA.add (UHA.add d v) p else e.state

end DIFD

/-! Evolution & Dynamics -/

structure Dynamics (n : Nat) where
  updateEntity   : Entity n → Word → Entity n
  updateEntropy  : FieldState n → Word
  updateTopology : Topology n → List (Entity n) → Topology n

structure Evolution (n : Nat) where
  mutate : Entity n → Entity n
  select : List (Entity n) → List (Entity n)
  adapt  : Entity n → Word → Entity n

structure EvolutionCore (n : Nat) where
  fitness   : Entity n → FieldState n → Word
  diversity : List (Entity n)

namespace Unified

variable {n : Nat}

def discreteToContinuous (d : Word) (x : UHA n) : UHA n :=
  UHA.smul (BSCM.entropy d) x

def continuousToDiscrete (x : UHA n) : Word :=
  BSCM.controlStep x.norm (BSCM.entropy x.norm)

end Unified

structure Engine (n : Nat) where
  dynamics  : Dynamics n
  evolution : Evolution n
  takeoCore : Option (EvolutionCore n)

def updateEntityUnified {n : Nat} (dyn : Dynamics n) (top : Topology n) (entropy : Word)
    (neighbors : List (Entity n)) (e : Entity n) : Entity n :=
  let fluidState := DIFD.fluidUpdate top entropy e neighbors
  let contState  := Unified.discreteToContinuous e.discrete fluidState
  let newDisc    := Unified.continuousToDiscrete contState
  let base       := dyn.updateEntity e entropy
  { base with state := contState, discrete := newDisc }

def stepClassic {n : Nat} (eng : Engine n) (s : FieldState n) : FieldState n :=
  let updated :=
    s.entities.map (fun e => updateEntityUnified eng.dynamics s.topology s.entropy s.entities e)
  let adapted  := updated.map (fun e => eng.evolution.adapt e s.entropy)
  let selected := eng.evolution.select adapted
  let mutated  := selected.map eng.evolution.mutate
  let newTopology := eng.dynamics.updateTopology s.topology mutated
  let interimState : FieldState n :=
    { entities := mutated, entropy := s.entropy, topology := newTopology }
  let newEntropy := eng.dynamics.updateEntropy interimState
  { entities := mutated, entropy := newEntropy, topology := newTopology }

def envChanged {n : Nat} (prev curr : FieldState n) : Bool :=
  decide (prev.entropy ≠ curr.entropy ∨
    prev.topology.viscosity ≠ curr.topology.viscosity ∨
    prev.topology.curvature ≠ curr.topology.curvature)

def stepTakeo {n : Nat} (_eng : Engine n) (core : EvolutionCore n)
    (prev curr : FieldState n) : FieldState n :=
  if envChanged prev curr then curr else prev

def step {n : Nat} (eng : Engine n) (s : FieldState n) : FieldState n :=
  match eng.takeoCore with
  | none => stepClassic eng s
  | some core => stepTakeo eng core s (stepClassic eng s)

/-!
============================================================
4. Physical AI Guard & Safety Layer (Fail-Closed)
============================================================
-/

structure Guarded (S : Type*) where
  propose : S → S
  fallback : S → S
  safe : S → Prop
  trusted : S → Prop
  fallback_safe : ∀ s, safe s → safe (fallback s)

noncomputable def Guarded.step {S : Type*} (G : Guarded S) (s : S) : S :=
  if G.trusted s ∧ G.safe (G.propose s) then G.propose s else G.fallback s

noncomputable def Guarded.run {S : Type*} (G : Guarded S) : Nat → S → S
  | 0, s => s
  | k + 1, s => Guarded.run G k (G.step s)

theorem Guarded.step_safe {S : Type*} (G : Guarded S) {s : S} (h : G.safe s) :
    G.safe (G.step s) := by
  unfold Guarded.step
  by_cases hc : G.trusted s ∧ G.safe (G.propose s)
  · rw [if_pos hc]
    exact hc.2
  · rw [if_neg hc]
    exact G.fallback_safe _ h

theorem Guarded.run_safe {S : Type*} (G : Guarded S) (k : Nat) :
    ∀ s, G.safe s → G.safe (G.run k s) := by
  induction k with
  | zero => intro s h; exact h
  | succ k ih =>
    intro s h
    show G.safe (G.run k (G.step s))
    exact ih _ (G.step_safe h)

structure SwarmLimits where
  vmax : Nat
  minEnergy : Nat
  maxRobots : Nat

def swarmSafe {n : Nat} (lim : SwarmLimits) (s : FieldState n) : Prop :=
  s.entities.length ≤ lim.maxRobots ∧
  ∀ e ∈ s.entities, lim.minEnergy ≤ e.fState.energy.val ∧ e.state.norm.val ≤ lim.vmax

def brakeEntity {n : Nat} (e : Entity n) : Entity n := { e with state := UHA.zero }

def brake {n : Nat} (s : FieldState n) : FieldState n :=
  { s with entities := s.entities.map brakeEntity }

theorem brake_safe {n : Nat} (lim : SwarmLimits) {s : FieldState n}
    (h : swarmSafe lim s) : swarmSafe lim (brake s) := by
  unfold swarmSafe at h ⊢
  refine ⟨?_, ?_⟩
  · show (s.entities.map brakeEntity).length ≤ lim.maxRobots
    rw [List.length_map]
    exact h.1
  · intro e he
    have he' : e ∈ s.entities.map brakeEntity := he
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he'
    refine ⟨(h.2 a ha).1, ?_⟩
    show (UHA.norm (UHA.zero : UHA n)).val ≤ lim.vmax
    rw [UHA.norm_zero, ZMod.val_zero]
    exact Nat.zero_le _

noncomputable def swarmGuard {n : Nat} (eng : Engine n) (lim : SwarmLimits)
    (trusted : FieldState n → Prop) : Guarded (FieldState n) where
  propose := ACMTY.step eng
  fallback := brake
  safe := swarmSafe lim
  trusted := trusted
  fallback_safe := fun _ h => brake_safe lim h

theorem swarm_safe_forever {n : Nat} (eng : Engine n) (lim : SwarmLimits)
    (trusted : FieldState n → Prop) (k : Nat) (s : FieldState n)
    (h : swarmSafe lim s) : swarmSafe lim ((swarmGuard eng lim trusted).run k s) :=
  (swarmGuard eng lim trusted).run_safe k s h

end ACMTY
end UnifiedPhysicalAI
