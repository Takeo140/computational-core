/-
  ACM-TY: Abstract Computation Model — Takeo Yamamoto
  完全版 Lean 4 実装（補完版）
  UHA × BSCM × DIFD × GIFE × Evolution
  License: Apache 2.0
  Author: Takeo Yamamoto

  方針:
  * 基底核の型は ZMod (2^64)（BitVec 64 との橋渡し補題は後続）
  * まず基底核（UHA の加法・スカラー倍・mulWith・Module・双線形性）を完成
  * ZMod には `%` `/` `<` `&&&` `>>>` が無いので、すべて `.val : Nat` 経由で定義
-/

import Mathlib

/-## 0. 基本定義 -/

abbrev U64 := ZMod (2 ^ 64)

/-- 任意の自然数を `Fin n` に（mod n で）落とす。n ≠ 0 が必要。 -/
def finOfNat (n : Nat) [NeZero n] (k : Nat) : Fin n :=
  ⟨k % n, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne n))⟩

/-! ## 1. UHA — UltraCore HyperAlgebra（連続核） -/

@[ext]
structure UHA (n : Nat) where
  coords : Fin n → U64

namespace UHA

variable {n : Nat}

/-- 加算 -/
def add (x y : UHA n) : UHA n :=
  ⟨fun i => x.coords i + y.coords i⟩

/-- スカラー倍 -/
def smul (a : U64) (x : UHA n) : UHA n :=
  ⟨fun i => a * x.coords i⟩

instance : AddCommGroup (UHA n) where
  add := UHA.add
  zero := ⟨fun _ => 0⟩
  neg := fun x => ⟨fun i => - x.coords i⟩
  add_assoc := fun x y z => by
    ext i
    show x.coords i + y.coords i + z.coords i = x.coords i + (y.coords i + z.coords i)
    ring
  zero_add := fun x => by
    ext i
    show 0 + x.coords i = x.coords i
    ring
  add_zero := fun x => by
    ext i
    show x.coords i + 0 = x.coords i
    ring
  neg_add_cancel := fun x => by
    ext i
    show - x.coords i + x.coords i = 0
    ring
  add_comm := fun x y => by
    ext i
    show x.coords i + y.coords i = y.coords i + x.coords i
    ring

instance : Module U64 (UHA n) where
  smul := UHA.smul
  one_smul := fun x => by
    ext i
    show (1 : U64) * x.coords i = x.coords i
    ring
  mul_smul := fun a b x => by
    ext i
    show a * b * x.coords i = a * (b * x.coords i)
    ring
  smul_zero := fun a => by
    ext i
    show a * 0 = 0
    ring
  smul_add := fun a x y => by
    ext i
    show a * (x.coords i + y.coords i) = a * x.coords i + a * y.coords i
    ring
  add_smul := fun a b x => by
    ext i
    show (a + b) * x.coords i = a * x.coords i + b * x.coords i
    ring
  zero_smul := fun x => by
    ext i
    show (0 : U64) * x.coords i = 0
    ring

@[simp] theorem coords_add (x y : UHA n) (i : Fin n) :
    (x + y).coords i = x.coords i + y.coords i := rfl

@[simp] theorem coords_zero (i : Fin n) : (0 : UHA n).coords i = 0 := rfl

@[simp] theorem coords_neg (x : UHA n) (i : Fin n) :
    (-x).coords i = - x.coords i := rfl

@[simp] theorem coords_smul (a : U64) (x : UHA n) (i : Fin n) :
    (a • x).coords i = a * x.coords i := rfl

theorem add_def (x y : UHA n) : x + y = UHA.add x y := rfl
theorem smul_def (a : U64) (x : UHA n) : a • x = UHA.smul a x := rfl

/-- 多元代数乗法（構造定数 c を外部から与える） -/
def mulWith
    (c : Fin n → Fin n → UHA n)
    (x y : UHA n) : UHA n :=
  ⟨fun i =>
    ∑ j : Fin n, ∑ k : Fin n, (x.coords j) * (y.coords k) * (c j k).coords i⟩

/-- ノルム（量子状態の離散版） -/
def norm (x : UHA n) : U64 :=
  ∑ i : Fin n, (x.coords i) * (x.coords i)

/-- 例：対角型の構造定数（成分ごとの積）。 -/
def diagConst (n : Nat) : Fin n → Fin n → UHA n :=
  fun j k => ⟨fun i => if j = k ∧ k = i then (1 : U64) else 0⟩

/-! ### 双線形性 -/

theorem mulWith_add_left (c : Fin n → Fin n → UHA n) (x x' y : UHA n) :
    mulWith c (x + x') y = mulWith c x y + mulWith c x' y := by
  ext i
  simp [mulWith, add_mul, Finset.sum_add_distrib]

theorem mulWith_add_right (c : Fin n → Fin n → UHA n) (x y y' : UHA n) :
    mulWith c x (y + y') = mulWith c x y + mulWith c x y' := by
  ext i
  simp [mulWith, mul_add, add_mul, Finset.sum_add_distrib]

theorem mulWith_smul_left (c : Fin n → Fin n → UHA n) (a : U64) (x y : UHA n) :
    mulWith c (a • x) y = a • mulWith c x y := by
  ext i
  simp only [mulWith, coords_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem mulWith_smul_right (c : Fin n → Fin n → UHA n) (a : U64) (x y : UHA n) :
    mulWith c x (a • y) = a • mulWith c x y := by
  ext i
  simp only [mulWith, coords_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

/-- `mulWith` を U64 上の双線形写像として束ねたもの。 -/
def mulLinear (c : Fin n → Fin n → UHA n) :
    UHA n →ₗ[U64] UHA n →ₗ[U64] UHA n :=
  LinearMap.mk₂ U64 (mulWith c)
    (mulWith_add_left c) (mulWith_smul_left c)
    (mulWith_add_right c) (mulWith_smul_right c)

/-! ### ノルムの基本性質 -/

theorem norm_zero : norm (0 : UHA n) = 0 := by
  simp [norm]

theorem norm_smul (a : U64) (x : UHA n) : norm (a • x) = a * a * norm x := by
  simp only [norm, coords_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end UHA

/-- ユニタリ作用素（量子ゲートの離散版） -/
structure UHA.UOp (n : Nat) where
  f : UHA n → UHA n
  unitary_like : ∀ v, UHA.norm (f v) = UHA.norm v

namespace UHA.UOp

variable {n : Nat}

def id (n : Nat) : UOp n := ⟨fun v => v, fun _ => rfl⟩

def comp (g f : UOp n) : UOp n :=
  ⟨fun v => g.f (f.f v), fun v => (g.unitary_like (f.f v)).trans (f.unitary_like v)⟩

end UHA.UOp

instance {n : Nat} : Repr (UHA n) where
  reprPrec x _ := Std.Format.text (toString (List.ofFn fun i => (x.coords i).val))

/-! ## 2. BSCM — Discrete Control Core（離散核） -/

namespace BSCM

/-- 離散状態更新（偶数なら半分、奇数なら (s+1)/2）。Nat 上で計算して U64 に戻す。 -/
def delta (s : U64) : U64 :=
  if s.val % 2 = 0 then
    ((s.val / 2 : Nat) : U64)
  else
    (((s.val + 1) / 2 : Nat) : U64)

/-- 外部入力付き制御ステップ -/
def controlStep (current_state external_input : U64) : U64 :=
  delta (current_state + external_input)

/-- 簡易エントロピー指標（下位2バイトの和）。`&&& 255` = `% 256`、`>>> 8` = `/ 256`。 -/
def entropy (s : U64) : U64 :=
  (((s.val % 256) + ((s.val / 256) % 256) : Nat) : U64)

end BSCM

/-! ## 3. GIFE — General Information Field Engine（場核） -/

structure Entity (n : Nat) where
  id       : Nat
  state    : UHA n
  energy   : U64
  mood     : U64
  genome   : U64
  discrete : U64

instance {n : Nat} : Repr (Entity n) where
  reprPrec e _ :=
    Std.Format.text
      s!"Entity(id={e.id}, energy={e.energy.val}, mood={e.mood.val}, genome={e.genome.val}, discrete={e.discrete.val}, state={toString (repr e.state)})"

/-- Topology：固定行列による接続構造 -/
structure Topology (n : Nat) where
  connMatrix : Fin n → Fin n → U64
  viscosity  : U64
  curvature  : U64

instance {n : Nat} : Repr (Topology n) where
  reprPrec t _ :=
    Std.Format.text s!"Topology(viscosity={t.viscosity.val}, curvature={t.curvature.val})"

namespace Topology

variable {n : Nat}

/-- i→j の接続強度 -/
def conn (top : Topology n) (i j : Fin n) : U64 :=
  top.connMatrix i j

end Topology

structure FieldState (n : Nat) where
  entities : List (Entity n)
  entropy  : U64
  topology : Topology n

instance {n : Nat} : Repr (FieldState n) where
  reprPrec s _ :=
    let es := s.entities.map (fun e => toString (repr e))
    Std.Format.text
      s!"FieldState(entropy={s.entropy.val}, topology={toString (repr s.topology)}, entities={es})"

/-! ## 4. DIFD — Discrete Fluid Dynamics（流体核） -/

namespace DIFD

variable {n : Nat}

/-- 粘性クリップ（上限 10^6） -/
def clipViscosity (v : U64) : U64 :=
  if 1000000 < v.val then (1000000 : U64) else v

/-- 渦度減衰 -/
def decayVortex (c : U64) : U64 :=
  ((c.val / 2 : Nat) : U64)

/-- 圧力正規化（上限 10^12） -/
def normalizePressure (p : U64) : U64 :=
  if 10 ^ 12 < p.val then ((10 ^ 12 : Nat) : U64) else p

/-- CFL 条件（簡易版）。Nat 上で比較するのでラップアラウンドしない。 -/
def cfl (vel : UHA n) (visc : U64) : Bool :=
  decide ((UHA.norm vel).val < visc.val * visc.val)

/-- 離散拡散：隣接 Entity の UHA 状態を重み付き平均（整数除算）。 -/
def diffuse [NeZero n]
    (top : Topology n)
    (e : Entity n)
    (neighbors : List (Entity n)) : UHA n :=
  let w : Entity n → U64 := fun nb =>
    Topology.conn top (finOfNat n e.id) (finOfNat n nb.id)
  let total : UHA n :=
    neighbors.foldl
      (fun acc nb => UHA.add acc (UHA.smul (w nb) nb.state))
      ⟨fun _ => 0⟩
  let wsum : U64 :=
    neighbors.foldl (fun a nb => a + w nb) 0
  if wsum = 0 then e.state
  else ⟨fun i => (((total.coords i).val / wsum.val : Nat) : U64)⟩

/-- 離散渦度 -/
def vortex (top : Topology n) (e : Entity n) : UHA n :=
  UHA.smul (decayVortex top.curvature) e.state

/-- 離散圧力 -/
def pressure (entropy : U64) (e : Entity n) : UHA n :=
  UHA.smul (normalizePressure entropy) e.state

/-- 完成版流体更新則 -/
def fluidUpdate [NeZero n]
    (top : Topology n)
    (entropy : U64)
    (e : Entity n)
    (neighbors : List (Entity n)) : UHA n :=
  let visc := clipViscosity top.viscosity
  let d    := diffuse top e neighbors
  let v    := vortex top e
  let p    := pressure entropy e
  if cfl d visc then
    UHA.add (UHA.add d v) p
  else
    e.state

end DIFD

/-! ## 5. Dynamics & Evolution（力学核＋進化核） -/

structure Dynamics (n : Nat) where
  updateEntity   : Entity n → U64 → Entity n
  updateEntropy  : FieldState n → U64
  updateTopology : Topology n → List (Entity n) → Topology n

structure Evolution (n : Nat) where
  mutate : Entity n → Entity n
  select : List (Entity n) → List (Entity n)
  adapt  : Entity n → U64 → Entity n

structure EvolutionCore (n : Nat) where
  fitness   : Entity n → FieldState n → U64
  diversity : List (Entity n)

/-- 生存選択：エネルギー非ゼロのみ残す（全滅するなら元の集団を保持）。 -/
def selectAlive {n : Nat} (es : List (Entity n)) : List (Entity n) :=
  match es.filter (fun e => decide (e.energy ≠ 0)) with
  | [] => es
  | l  => l

/-- 既定の力学：エネルギーを BSCM 制御ステップで更新、場エントロピーは
    各 Entity の離散エントロピーの総和、トポロジーは不変。 -/
def Dynamics.default (n : Nat) : Dynamics n where
  updateEntity   := fun e ent => { e with energy := BSCM.controlStep e.energy ent }
  updateEntropy  := fun s => s.entities.foldl (fun a e => a + BSCM.entropy e.discrete) 0
  updateTopology := fun top _ => top

/-- 既定の進化：LCG による遺伝子変異、mood の適応、生存選択。 -/
def Evolution.default (n : Nat) : Evolution n where
  mutate := fun e =>
    { e with genome := e.genome * 6364136223846793005 + 1442695040888963407 }
  select := selectAlive
  adapt  := fun e ent => { e with mood := BSCM.controlStep e.mood ent }

/-- 既定の進化核：適応度 = energy + 環境エントロピー由来の項。 -/
def EvolutionCore.default {n : Nat} (pool : List (Entity n)) : EvolutionCore n where
  fitness   := fun e env => e.energy + BSCM.entropy (e.discrete + env.entropy)
  diversity := pool

/-! ## 6. BSCM ↔ UHA 統合（離散と連続の結合） -/

namespace Unified

variable {n : Nat}

/-- 離散 → 連続 -/
def discreteToContinuous (d : U64) (x : UHA n) : UHA n :=
  UHA.smul (BSCM.entropy d) x

/-- 連続 → 離散 -/
def continuousToDiscrete (x : UHA n) : U64 :=
  BSCM.controlStep (UHA.norm x) (BSCM.entropy (UHA.norm x))

end Unified

/-! ## 7. Engine & 統合ステップ -/

structure Engine (n : Nat) where
  dynamics  : Dynamics n
  evolution : Evolution n
  takeoCore : Option (EvolutionCore n)

/-- 既定エンジン（Takeo 進化なし）。 -/
def Engine.default (n : Nat) : Engine n :=
  { dynamics := Dynamics.default n
    evolution := Evolution.default n
    takeoCore := none }

/-- 統合 Entity 更新（DIFD + BSCM-UHA） -/
def updateEntityUnified {n : Nat} [NeZero n]
    (dyn : Dynamics n)
    (top : Topology n)
    (entropy : U64)
    (neighbors : List (Entity n))
    (e : Entity n) : Entity n :=
  let fluidState := DIFD.fluidUpdate top entropy e neighbors
  let contState  := Unified.discreteToContinuous e.discrete fluidState
  let newDisc    := Unified.continuousToDiscrete contState
  let base       := dyn.updateEntity e entropy
  { base with state := contState, discrete := newDisc }

/-- 従来進化ステップ（GIFE + DIFD + Evolution + BSCM-UHA） -/
def stepClassic {n : Nat} [NeZero n] (eng : Engine n) (s : FieldState n) : FieldState n :=
  let updated :=
    s.entities.map (fun e =>
      updateEntityUnified eng.dynamics s.topology s.entropy s.entities e)
  let adapted :=
    updated.map (fun e => eng.evolution.adapt e s.entropy)
  let selected :=
    eng.evolution.select adapted
  let mutated :=
    selected.map eng.evolution.mutate
  let newTopology :=
    eng.dynamics.updateTopology s.topology mutated
  let interimState : FieldState n :=
    { entities := mutated, entropy := s.entropy, topology := newTopology }
  let newEntropy :=
    eng.dynamics.updateEntropy interimState
  { entities := mutated, entropy := newEntropy, topology := newTopology }

/-! ## 8. Takeo Evolution（環境変化時のみ進化） -/

def envChanged {n : Nat} (prev curr : FieldState n) : Bool :=
  decide (prev.entropy ≠ curr.entropy ∨
          prev.topology.viscosity ≠ curr.topology.viscosity ∨
          prev.topology.curvature ≠ curr.topology.curvature)

def argmaxEntity {n : Nat}
    (core : EvolutionCore n)
    (env  : FieldState n) : Entity n :=
  match core.diversity with
  | []      =>
    { id := 0, state := ⟨fun _ => 0⟩, energy := 0, mood := 0, genome := 0, discrete := 0 }
  | e :: es =>
    es.foldl
      (fun best cand =>
        if (core.fitness best env).val < (core.fitness cand env).val then cand else best)
      e

/-- Takeo モデル：環境変化時のみ進化を適用 -/
def stepTakeo {n : Nat}
    (_eng  : Engine n)
    (core : EvolutionCore n)
    (prev : FieldState n)
    (curr : FieldState n) : FieldState n :=
  if envChanged prev curr then
    let best := argmaxEntity core curr
    { entities := [best]
      entropy  := curr.entropy
      topology := curr.topology }
  else prev

/-- 統合ステップ：Takeo 進化あり／なしを切り替え -/
def step {n : Nat} [NeZero n] (eng : Engine n) (s : FieldState n) : FieldState n :=
  match eng.takeoCore with
  | none      => stepClassic eng s
  | some core =>
    let next := stepClassic eng s
    stepTakeo eng core s next

/-- k ステップ反復 -/
def run {n : Nat} [NeZero n] (eng : Engine n) : Nat → FieldState n → FieldState n
  | 0,     s => s
  | k + 1, s => run eng k (step eng s)

/-! ### ステップ則の基本性質 -/

theorem step_none {n : Nat} [NeZero n] (eng : Engine n)
    (h : eng.takeoCore = none) (s : FieldState n) :
    step eng s = stepClassic eng s := by
  simp [step, h]

theorem stepTakeo_unchanged {n : Nat} (eng : Engine n) (core : EvolutionCore n)
    (prev curr : FieldState n) (h : envChanged prev curr = false) :
    stepTakeo eng core prev curr = prev := by
  simp [stepTakeo, h]

theorem stepTakeo_changed_entities {n : Nat} (eng : Engine n) (core : EvolutionCore n)
    (prev curr : FieldState n) (h : envChanged prev curr = true) :
    (stepTakeo eng core prev curr).entities = [argmaxEntity core curr] := by
  simp [stepTakeo, h]

/-! ## 9. 簡易テスト -/

def sampleUHA : UHA 4 :=
  ⟨fun i =>
    match i.1 with
    | 0 => 1
    | 1 => 2
    | 2 => 3
    | _ => 4⟩

#eval (UHA.norm sampleUHA).val                    -- 30
#eval repr (UHA.mulWith (UHA.diagConst 4) sampleUHA sampleUHA)  -- [1, 4, 9, 16]
#eval (BSCM.delta 7).val                          -- 4
#eval (BSCM.entropy 0x0102).val                   -- 3

def sampleEntity (k : Nat) : Entity 4 :=
  { id := k
    state := ⟨fun i => ((i.1 + k + 1 : Nat) : U64)⟩
    energy := ((10 + k : Nat) : U64)
    mood := 0
    genome := (k : U64)
    discrete := ((k + 1 : Nat) : U64) }

def sampleTopology : Topology 4 :=
  { connMatrix := fun _ _ => 1, viscosity := 1000, curvature := 8 }

def sampleField : FieldState 4 :=
  { entities := [sampleEntity 0, sampleEntity 1, sampleEntity 2]
    entropy := 5
    topology := sampleTopology }

#eval repr (run (Engine.default 4) 3 sampleField)

/-- Takeo 進化ありのエンジン -/
def sampleEngineTakeo : Engine 4 :=
  { Engine.default 4 with takeoCore := some (EvolutionCore.default sampleField.entities) }

#eval repr (run sampleEngineTakeo 3 sampleField)
