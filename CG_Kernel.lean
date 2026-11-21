License Apache-2.0  Takeo Yamamoto
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace CGKernel

open BigOperators Finset Matrix

abbrev Vec (n : Nat) := Fin n → ℝ
abbrev Mat (n : Nat) := Matrix (Fin n) (Fin n) ℝ

/-- ユークリッド内積 ⟨u, v⟩ -/
noncomputable def inner {n : Nat} (u v : Vec n) : ℝ :=
  ∑ i : Fin n, u i * v i

/-- 行列ベクトル積 A v -/
noncomputable def matVec {n : Nat} (A : Mat n) (v : Vec n) : Vec n :=
  A *ᵥ v

/-- ステップ幅 α_k = ⟨r_k, r_k⟩ / ⟨p_k, A p_k⟩ -/
noncomputable def stepAlpha {n : Nat} (A : Mat n) (r p : Vec n) : ℝ :=
  inner r r / inner p (matVec A p)

/-- 次反復の探索方向係数 β_k = ⟨r_{k+1}, r_{k+1}⟩ / ⟨r_k, r_k⟩ -/
noncomputable def nextBeta {n : Nat} (rNext rCurr : Vec n) : ℝ :=
  inner rNext rNext / inner rCurr rCurr

/-- CG法 1反復カーネル：現在の (x, r, p) から次の (x', r', p') を算出 -/
noncomputable def cgStep {n : Nat} (A : Mat n) (x r p : Vec n) :
    Vec n × Vec n × Vec n :=
  let Ap := matVec A p
  let α := stepAlpha A r p
  let xNext : Vec n := fun i => x i + α * p i
  let rNext : Vec n := fun i => r i - α * Ap i
  let β := nextBeta rNext r
  let pNext : Vec n := fun i => rNext i + β * p i
  (xNext, rNext, pNext)

/-- 残差の更新則：r_{k+1} = r_k - α_k (A p_k) が成分ごとに成り立つこと -/
theorem cgStep_residual_update {n : Nat} (A : Mat n) (x r p : Vec n) (i : Fin n) :
    (cgStep A x r p).2.1 i = r i - stepAlpha A r p * (matVec A p) i := by
  simp [cgStep]

/-- 残差更新の両辺に A⁻¹ の代わりに内積をとったときの線形分解 -/
theorem inner_residual_next {n : Nat} (A : Mat n) (x r p w : Vec n)
    (hAp : inner p (matVec A p) ≠ 0) :
    inner ((cgStep A x r p).2.1) w =
      inner r w - (inner r r / inner p (matVec A p)) * inner (matVec A p) w := by
  have hα : stepAlpha A r p = inner r r / inner p (matVec A p) := rfl
  simp only [cgStep, inner, hα, sub_mul, Finset.sum_sub_distrib]
  refine congrArg (fun s => (∑ i : Fin n, r i * w i) - s) ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end CGKernel
