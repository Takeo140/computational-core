License Apache-2.0  Takeo Yamamoto
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Ring.Defs

namespace DiscreteComplexLA

/-- 64ビット離散環 `ZMod (2^64)` 上の離散複素数 -/
structure DComplex where
  re : ZMod (2 ^ 64)
  im : ZMod (2 ^ 64)
  deriving DecidableEq, Repr

namespace DComplex

def zero : DComplex := ⟨0, 0⟩
def one : DComplex := ⟨1, 0⟩
def i : DComplex := ⟨0, 1⟩

instance : Zero DComplex := ⟨zero⟩
instance : One DComplex := ⟨one⟩

def add (z w : DComplex) : DComplex :=
  ⟨z.re + w.re, z.im + w.im⟩

def sub (z w : DComplex) : DComplex :=
  ⟨z.re - w.re, z.im - w.im⟩

def neg (z : DComplex) : DComplex :=
  ⟨-z.re, -z.im⟩

def conj (z : DComplex) : DComplex :=
  ⟨z.re, -z.im⟩

/-- 離散複素乗算：(a + bi)(c + di) = (ac - bd) + (ad + bc)i -/
def mul (z w : DComplex) : DComplex :=
  ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩

instance : Add DComplex := ⟨add⟩
instance : Sub DComplex := ⟨sub⟩
instance : Neg DComplex := ⟨neg⟩
instance : Mul DComplex := ⟨mul⟩

/-- ノルム平方（離散環 `ZMod (2^64)` 内の `|z|^2 = re^2 + im^2`） -/
def normSq (z : DComplex) : ZMod (2 ^ 64) :=
  z.re * z.re + z.im * z.im

theorem add_comm (z w : DComplex) : z + w = w + z := by
  ext <;> exact _root_.add_comm _ _

theorem add_assoc (u v w : DComplex) : (u + v) + w = u + (v + w) := by
  ext <;> exact _root_.add_assoc _ _ _

theorem zero_add (z : DComplex) : (0 : DComplex) + z = z := by
  ext <;> exact _root_.zero_add _

theorem add_zero (z : DComplex) : z + (0 : DComplex) = z := by
  ext <;> exact _root_.add_zero _

theorem conj_conj (z : DComplex) : conj (conj z) = z := by
  ext <;> simp [conj]

theorem conj_add (z w : DComplex) : conj (z + w) = conj z + conj w := by
  ext <;> simp [conj, add, neg_add]

theorem mul_comm (z w : DComplex) : z * w = w * z := by
  ext <;> dsimp [mul]
  · rw [_root_.mul_comm z.re w.re, _root_.mul_comm z.im w.im]
  · rw [_root_.mul_comm z.re w.im, _root_.mul_comm z.im w.re, _root_.add_comm]

theorem mul_one (z : DComplex) : z * (1 : DComplex) = z := by
  ext <;> simp [mul, one]

end DComplex

/-- 長さ `n` の離散複素ベクトル -/
abbrev DVec (n : Nat) := Fin n → DComplex

/-- `m × n` の離散複素行列 -/
abbrev DMat (m n : Nat) := Fin m → Fin n → DComplex

namespace DVec

def zero (n : Nat) : DVec n := fun _ => 0

def add {n : Nat} (u v : DVec n) : DVec n := fun i => u i + v i

def scale {n : Nat} (c : DComplex) (v : DVec n) : DVec n := fun i => c * v i

/-- 離散エルミート内積 `<u, v> = ∑ i, conj (u i) * v i` -/
def inner {n : Nat} (u v : DVec n) : DComplex :=
  Finset.univ.sum fun i => DComplex.conj (u i) * v i

theorem add_comm {n : Nat} (u v : DVec n) : add u v = add v u := by
  funext i
  exact DComplex.add_comm (u i) (v i)

theorem scale_add {n : Nat} (c : DComplex) (u v : DVec n) :
    scale c (add u v) = add (scale c u) (scale c v) := by
  funext i
  dsimp [scale, add, DComplex.mul, DComplex.add]
  ext <;> ring

end DVec

namespace DMat

def zero (m n : Nat) : DMat m n := fun _ _ => 0

def add {m n : Nat} (A B : DMat m n) : DMat m n := fun i j => A i j + B i j

def scale {m n : Nat} (c : DComplex) (A : DMat m n) : DMat m n :=
  fun i j => c * A i j

/-- 転置行列 `Aᵀ` -/
def transpose {m n : Nat} (A : DMat m n) : DMat n m := fun i j => A j i

/-- 随伴行列（共役転置 `Aᴴ`） -/
def adjoint {m n : Nat} (A : DMat m n) : DMat n m :=
  fun i j => DComplex.conj (A j i)

/-- 行列とベクトルの積 `A *ᵥ x` -/
def mulVec {m n : Nat} (A : DMat m n) (x : DVec n) : DVec m :=
  fun i => Finset.univ.sum fun j => A i j * x j

/-- 行列積 `A *ₘ B` -/
def mulMat {m k n : Nat} (A : DMat m k) (B : DMat k n) : DMat m n :=
  fun i j => Finset.univ.sum fun p => A i p * B p j

theorem adjoint_adjoint {m n : Nat} (A : DMat m n) :
    adjoint (adjoint A) = A := by
  funext i j
  exact DComplex.conj_conj (A i j)

theorem mulVec_add {m n : Nat} (A : DMat m n) (x y : DVec n) :
    mulVec A (DVec.add x y) = DVec.add (mulVec A x) (mulVec A y) := by
  funext i
  dsimp [mulVec, DVec.add]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  dsimp [DComplex.mul, DComplex.add]
  ext <;> ring

end DMat

end DiscreteComplexLA
