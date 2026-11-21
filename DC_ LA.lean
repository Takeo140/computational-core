License Apache-2.0  Takeo Yamamoto
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic

namespace DiscreteComplexLA

structure DComplex where
  re : ZMod (2 ^ 64)
  im : ZMod (2 ^ 64)
  deriving DecidableEq, Repr

namespace DComplex

def zero : DComplex := ⟨0, 0⟩
def one : DComplex := ⟨1, 0⟩
def negOne : DComplex := ⟨-1, 0⟩

instance : Zero DComplex := ⟨zero⟩
instance : One DComplex := ⟨one⟩

def add (z w : DComplex) : DComplex := ⟨z.re + w.re, z.im + w.im⟩
def sub (z w : DComplex) : DComplex := ⟨z.re - w.re, z.im - w.im⟩
def neg (z : DComplex) : DComplex := ⟨-z.re, -z.im⟩
def conj (z : DComplex) : DComplex := ⟨z.re, -z.im⟩
def mul (z w : DComplex) : DComplex :=
  ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩

instance : Add DComplex := ⟨add⟩
instance : Sub DComplex := ⟨sub⟩
instance : Neg DComplex := ⟨neg⟩
instance : Mul DComplex := ⟨mul⟩

@[simp]
lemma conj_conj (z : DComplex) : conj (conj z) = z := by
  ext <;> simp [conj]

@[simp]
lemma zero_mul (z : DComplex) : (0 : DComplex) * z = 0 := by
  ext <;> simp [mul]

@[simp]
lemma mul_zero (z : DComplex) : z * (0 : DComplex) = 0 := by
  ext <;> simp [mul]

@[simp]
lemma one_mul (z : DComplex) : (1 : DComplex) * z = z := by
  ext <;> simp [mul, one]

@[simp]
lemma mul_one (z : DComplex) : z * (1 : DComplex) = z := by
  ext <;> simp [mul, one]

@[simp]
lemma add_zero (z : DComplex) : z + (0 : DComplex) = z := by
  ext <;> simp [add]

@[simp]
lemma zero_add (z : DComplex) : (0 : DComplex) + z = z := by
  ext <;> simp [add]

end DComplex

abbrev DVec (n : Nat) := Fin n → DComplex
abbrev DMat (m n : Nat) := Fin m → Fin n → DComplex

namespace DMat

def mulMat {m k n : Nat} (A : DMat m k) (B : DMat k n) : DMat m n :=
  fun i j => Finset.univ.sum fun p => A i p * B p j

def mulVec {m n : Nat} (A : DMat m n) (x : DVec n) : DVec m :=
  fun i => Finset.univ.sum fun j => A i j * x j

def adjoint {m n : Nat} (A : DMat m n) : DMat n m :=
  fun i j => DComplex.conj (A j i)

def eye (n : Nat) : DMat n n :=
  fun i j => if i = j then 1 else 0

/-- クロネッカー積（テンソル積）：`(A ⊗ B)_{(r1, r2), (c1, c2)} = A_{r1, c1} * B_{r2, c2}` -/
def kron {m₁ n₁ m₂ n₂ : Nat} (A : DMat m₁ n₁) (B : DMat m₂ n₂) :
    DMat (m₁ * m₂) (n₁ * n₂) :=
  fun r c =>
    have hr1 : r.val / m₂ < m₁ := by
      apply Nat.div_lt_of_lt_mul
      simpa [Nat.mul_comm] using r.isLt
    have hr2 : r.val % m₂ < m₂ := Nat.mod_lt _ (by
      by_contra h
      simp at h
      subst h
      have := r.isLt
      simp at this)
    have hc1 : c.val / n₂ < n₁ := by
      apply Nat.div_lt_of_lt_mul
      simpa [Nat.mul_comm] using c.isLt
    have hc2 : c.val % n₂ < n₂ := Nat.mod_lt _ (by
      by_contra h
      simp at h
      subst h
      have := c.isLt
      simp at this)
    A ⟨r.val / m₂, hr1⟩ ⟨c.val / n₂, hc1⟩ * B ⟨r.val % m₂, hr2⟩ ⟨c.val % n₂, hc2⟩

end DMat

namespace DiscreteQuantumComp

/-- `n` 量子ビットの離散状態ベクトル（状態空間の次元は `2 ^ n`） -/
abbrev QState (n : Nat) := DVec (2 ^ n)

/-- `n` 量子ビットの離散ゲート演算子 -/
abbrev QGate (n : Nat) := DMat (2 ^ n) (2 ^ n)

/-- 計算基底状態 `|k⟩` -/
def basisState {n : Nat} (k : Fin (2 ^ n)) : QState n :=
  fun i => if i = k then 1 else 0

def ket0 : QState 1 := basisState ⟨0, by decide⟩
def ket1 : QState 1 := basisState ⟨1, by decide⟩

/-- 離散パウリ X ゲート（ビット反転）：`|0⟩ ↔ |1⟩` -/
def pauliX : QGate 1 :=
  fun i j =>
    if i.val = 0 ∧ j.val = 1 then 1
    else if i.val = 1 ∧ j.val = 0 then 1
    else 0

/-- 離散パウリ Z ゲート（位相反転）：`|0⟩ → |0⟩, |1⟩ → -|1⟩` -/
def pauliZ : QGate 1 :=
  fun i j =>
    if i.val = 0 ∧ j.val = 0 then 1
    else if i.val = 1 ∧ j.val = 1 then DComplex.negOne
    else 0

/-- 離散アダマール構造行列（正規化係数 `1/√2` を除いた離散環上の符号変換行列） -/
def hadamardD : QGate 1 :=
  fun i j =>
    if i.val = 1 ∧ j.val = 1 then DComplex.negOne else 1

/-- 2量子ビット CNOT ゲート（制御ビット=上位ビット `b / 2`、標的ビット=下位ビット `b % 2`） -/
def cnot : QGate 2 :=
  fun i j =>
    let ctrl_i := i.val / 2
    let tgt_i  := i.val % 2
    let ctrl_j := j.val / 2
    let tgt_j  := j.val % 2
    let expected_tgt := (ctrl_j + tgt_j) % 2
    if ctrl_i = ctrl_j ∧ tgt_i = expected_tgt then 1 else 0

/-- 量子ゲートの状態への作用 `|ψ'⟩ = U |ψ⟩` -/
def applyGate {n : Nat} (U : QGate n) (ψ : QState n) : QState n :=
  DMat.mulVec U ψ

/-- 離散ユニタリ性の条件：`Uᴴ *ₘ U = I` -/
def IsDiscreteUnitary {n : Nat} (U : QGate n) : Prop :=
  DMat.mulMat (DMat.adjoint U) U = DMat.eye (2 ^ n)

/-- パウリ X ゲートの自己逆元性：`X *ₘ X = I` -/
theorem pauliX_involutive : DMat.mulMat pauliX pauliX = DMat.eye 2 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [DMat.mulMat, DMat.eye, pauliX, Fin.sum_univ_two, DComplex.negOne] <;>
    decide

/-- パウリ Z ゲートの自己逆元性：`Z *ₘ Z = I` -/
theorem pauliZ_involutive : DMat.mulMat pauliZ pauliZ = DMat.eye 2 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [DMat.mulMat, DMat.eye, pauliZ, Fin.sum_univ_two, DComplex.negOne,
          DComplex.mul, DComplex.add] <;>
    decide

/-- 離散アダマール行列の自己随伴性（エルミート性）：`Hᴴ = H` -/
theorem hadamardD_hermitian : DMat.adjoint hadamardD = hadamardD := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [DMat.adjoint, hadamardD, DComplex.conj, DComplex.negOne]

end DiscreteQuantumComp
end DiscreteComplexLA
