-- Note this could all probably be defined better so that `prev` is such that
-- `prev n = m` such that `succ m = n`. This would make the proofs easier.


def PosNat := { n : Nat // n > 0 }

def prev (n : PosNat) : Nat := n.val - 1

theorem prev_eq_zero_iff_eq_one (n : PosNat) : prev n = 0 ↔ n.val = 1 := by
  apply Iff.intro
  { intro h
    have h1 : n.val - 1 = 0 := h
    have h2 : n.val = 1 := by
      calc
        n.val = n.val - 1 + 1 := by rw [Nat.sub_add_cancel n.property]
        _ = 1 := by rw [h1]
    exact h2
  }
  { intro h
    have h1 : prev n = 0 := by
      calc
        prev n = n.val - 1 := by rfl
         _ = 1 - 1 := by rw [h]
         _ = 0 := by rfl
    exact h1
  }

-- theorem prev_injective: ∀ n m: PosNat, prev n = prev m → n = m := by
--   intro n m h
--   have h1 : n.val - 1 = m.val - 1 := h
--   have h2 : n.val = Nat.succ n.val - 1 := by
--     rw [Nat.succ_sub_one n.val]
--   have h3 : m.val = Nat.succ m.val - 1 := by
--     rw [Nat.succ_sub_one m.val]
--   have h4 : n.val = m.val := by
--     calc
--       n.val = Nat.succ n.val - 1 := h2
--       _ = Nat.succ m.val - 1 := by rw [h1]

  -- have h2 : n.val = m.val := by
  --   calc
  --     n.val = Nat.succ (n.val - 1) by rw [Nat.succ_sub_one n.property]
    -- apply Nat.succ.inj
    -- rw [← Nat.succ_sub_one n.property, ← Nat.succ_sub_one m.property]
  -- exact Subtype.eq h2


-- theorem prev_well_defined: ∀ n: PosNat, prev n ≥ 0 := by
--   intro n
--   have h1 : n.val > 0 := n.property
--   have h2 : n.val ≠ 0 := Nat.pos_iff_ne_zero.mp h1
--   have h3 : ∃ m : Nat, n.val = Nat.succ m := by
--     apply Nat.exists_eq_succ_of_ne_zero
--     exact h2
--   sorry

def next (n : Nat) : PosNat := Subtype.mk (Nat.succ n) (Nat.succ_pos n)
