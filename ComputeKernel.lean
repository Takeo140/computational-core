License Apache-2.0  Takeo Yamamoto
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

namespace ComputeKernel

section FunctionalKernel

/-- 2つの配列（長さ `n` を想定）の内積を計算する計算カーネル -/
def dotArray (a b : Array Float) : Float :=
  let n := min a.size b.size
  Id.run do
    let mut acc : Float := 0.0
    for i in [:n] do
      acc := acc + a[i]! * b[i]!
    return acc

/-- 行優先（Row-major）で格納された `m × n` 行列 `A` とベクトル `x` の積 `y = A * x` -/
def matvecRowMajor (m n : Nat) (A x : Array Float) : Array Float :=
  Id.run do
    let mut y := Array.mkArray m 0.0
    for i in [:m] do
      let mut sum : Float := 0.0
      let rowOffset := i * n
      for j in [:n] do
        sum := sum + A[rowOffset + j]! * x[j]!
      y := y.set! i sum
    return y

end FunctionalKernel

section VerifiedSpec

open Matrix Finset

/-- 数学的な行列（`Fin m → Fin n → ℝ`）とベクトルの積 `mulVec` -/
noncomputable def exactMatVec {m n : Nat} (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) :
    Fin m → ℝ :=
  A *ᵥ x

/-- 数学的定義における `mulVec` の各成分は行ベクトルと `x` の内積に等しい -/
theorem exactMatVec_apply {m n : Nat} (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ)
    (i : Fin m) :
    exactMatVec A x i = ∑ j : Fin n, A i j * x j := by
  simp [exactMatVec, mulVec, dotProduct]

end VerifiedSpec

end ComputeKernel
