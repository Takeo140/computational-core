License Apache-2.0  Takeo Yamamoto
-- 完備束（Complete Lattice）上の単調写像に対する不動点の構成（Lean 4 / 自己完結）
structure CompleteLattice (α : Type) where
  le : α → α → Prop
  le_refl : ∀ x, le x x
  le_antisymm : ∀ {x y}, le x y → le y x → x = y
  le_trans : ∀ {x y z}, le x y → le y z → le x z
  sSup : (α → Prop) → α
  sSup_upper : ∀ (S : α → Prop) {x : α}, S x → le x (sSup S)
  sSup_least : ∀ (S : α → Prop) (m : α), (∀ x, S x → le x m) → le (sSup S) m

def Monotone {α : Type} (L : CompleteLattice α) (f : α → α) : Prop :=
  ∀ {x y}, L.le x y → L.le (f x) (f y)

def IsFixedPoint {α : Type} (L : CompleteLattice α) (f : α → α) (x : α) : Prop :=
  f x = x

-- 「x ≤ f x」を満たす元全体の集合（前不動点の一種）
def PostFixedSet {α : Type} (L : CompleteLattice α) (f : α → α) (x : α) : Prop :=
  L.le x (f x)

theorem monotone_has_fixed_point {α : Type} (L : CompleteLattice α) {f : α → α}
    (hf : Monotone L f) :
    ∃ x, IsFixedPoint L f x := by
  let S := PostFixedSet L f
  let g := L.sSup S
  refine ⟨g, ?_⟩
  -- 1. S の任意の元 x について x ≤ f x かつ x ≤ g なので、単調性より f x ≤ f g、推移律で x ≤ f g
  have hg_le_fg : L.le g (f g) := by
    apply L.sSup_least S (f g)
    intro x hx
    have hx_le_fx : L.le x (f x) := hx
    have hx_le_g : L.le x g := L.sSup_upper S hx
    have hfx_le_fg : L.le (f x) (f g) := hf hx_le_g
    exact L.le_trans hx_le_fx hfx_le_fg
  -- 2. g ≤ f g なので、単調性より f g ≤ f (f g)、つまり f g ∈ S
  have hfg_in_S : S (f g) := hf hg_le_fg
  -- 3. f g ∈ S なので上限性質より f g ≤ g
  have hfg_le_g : L.le (f g) g := L.sSup_upper S hfg_in_S
  -- 4. 反対称律より f g = g
  exact L.le_antisymm hfg_le_g hg_le_fg
