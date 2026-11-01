License Apache-2.0 Takeo Yamamoto
import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic

namespace ACM_TY

-- ============================================================================
-- 1. 物理・離散状態の定義 (State Space)
-- ============================================================================

structure EntityState where
  id : Nat
  energy : Nat
  positionNormSq : Nat
  deriving Repr, DecidableEq

structure SystemLimits where
  vmax : Nat
  minEnergy : Nat
  maxRobots : Nat
  deriving Repr

-- ============================================================================
-- 2. 安全不変量 (Safety Invariant / Fail-Closed Condition)
-- ============================================================================

-- 単体エンティティの安全条件
def isEntitySafe (e : EntityState) (limits : SystemLimits) : Prop :=
  e.energy >= limits.minEnergy ∧ e.positionNormSq <= limits.vmax

-- 群れ全体（Swarm）の安全条件
def isSwarmSafe (entities : List EntityState) (limits : SystemLimits) : Prop :=
  entities.length <= limits.maxRobots ∧ ∀ e ∈ entities, isEntitySafe e limits

-- ============================================================================
-- 3. ガード付き遷移関数 (Fail-Closed Firewall Transition)
-- ============================================================================

-- 外部からの未検証アクション（AIの提案・攻撃データ）を受信した際の更新ロジック
def proposeEntityTransition (e : EntityState) (untrustedAction : Nat) : EntityState :=
  { id := e.id,
    energy := e.energy + 1,
    positionNormSq := e.positionNormSq + untrustedAction }

def proposeSwarmTransition (entities : List EntityState) (untrustedAction : Nat) : List EntityState :=
  entities.map (fun e => proposeEntityTransition e untrustedAction)

-- セキュリティ・スーパーバイザー（Fail-Closed 防壁）
-- 提案された状態が安全条件を満たしていれば許可し、違反していれば即座にゼロ速度（Brake / Fallback）へフォールバックする
def guardedSupervisorStep (currentEntities : List EntityState) (untrustedAction : Nat) (limits : SystemLimits) : List EntityState :=
  let proposed := proposeSwarmTransition currentEntities untrustedAction
  if h : isSwarmSafe proposed limits then
    proposed  -- 安全保障通過：状態更新を許可
  else
    -- FAIL-CLOSED 発動：全機の位置変位をゼロ（Brake）に固定して隔離
    currentEntities.map (fun e => { e with positionNormSq := 0 })

-- ============================================================================
-- 4. セキュリティ定理の証明 (Theorem: Swarm Safe Forever)
-- ============================================================================

-- 補題：フォールバック（Brake）状態は常に安全不変量を満たす
theorem fallback_preserves_safety (currentEntities : List EntityState) (limits : SystemLimits)
    (h_len : currentEntities.length <= limits.maxRobots)
    (h_min_energy : ∀ e ∈ currentEntities, e.energy >= limits.minEnergy) :
    isSwarmSafe (currentEntities.map (fun e => { e with positionNormSq := 0 })) limits := by
  constructor
  · -- リストの長さは変わらないため制限内
    rw [List.length_map]
    exact h_len
  · -- 全てのエンティティの位置ノルムが 0 になり、エネルギーは維持されるため安全
    intro e he
    rw [List.mem_map] at he
    rcases he with ⟨orig, horig_mem, rfl⟩
    constructor
    · -- エネルギーはそのまま（>= minEnergy）
      exact h_min_energy orig horig_mem
    · -- 位置ノルムは 0 なので vmax 以下（vmaxが自然数である限り成立）
      exact Nat.zero_le limits.vmax

-- 主定理：任意の未検証アクション（攻撃・暴走指示）に対して、ガード付きステップは常に安全を保持する
theorem swarm_safe_forever (currentEntities : List EntityState) (untrustedAction : Nat) (limits : SystemLimits)
    (h_safe : isSwarmSafe currentEntities limits) :
    isSwarmSafe (guardedSupervisorStep currentEntities untrustedAction limits) limits := by
  dsimp [guardedSupervisorStep]
  split_ifs with h_cond
  · -- ケース A：提案された状態が安全条件をクリアした場合
    exact h_cond
  · -- ケース B：安全条件違反（攻撃検知・ハルシネーション）。Fail-Closed（ブレーキ）が作動
    rcases h_safe with ⟨h_len, h_all_safe⟩
    apply fallback_preserves_safety
    · exact h_len
    · intro e he
      exact (h_all_safe e he).1

end ACM_TY
