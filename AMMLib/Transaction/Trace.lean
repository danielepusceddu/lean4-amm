import AMMLib.Transaction.Deposit
import AMMLib.Transaction.Redeem
import AMMLib.Transaction.Swap.Basic
import AMMLib.Networth

/- Tx c init s is the type of all possible sequences
  of valid transactions that would result in s,
  starting from state init and with swaprate function sx -/
inductive Tx (sx: SX) (init: Γ): Γ → Type where
  -- The empty sequence brings you to the initial state
  | empty: Tx sx init init

  -- Sequence with a valid Deposit0 at the end
  | dep0 (s': Γ) (rs: Tx sx init s')
         (d0: Deposit0 s' t0 t1 a r0 r1):
      Tx sx init d0.apply

  -- Sequence with a valid Deposit at the end
  | dep (s': Γ) (rs: Tx sx init s')
        (d: Deposit s' a t0 t1 v0):
      Tx sx init d.apply

  -- Sequence with a valid Redeem at the end
  | red (s': Γ) (rs: Tx sx init s')
        (r: Redeem s' a t0 t1 v0):
      Tx sx init r.apply

  -- Sequence with a valid Swap at the end
  | swap (s': Γ) (rs: Tx sx init s')
         (sw: Swap sx s' a t0 t1 v0):
      Tx sx init sw.apply

def validInit (s: Γ): Prop :=
  (s.amms = Sₐ.empty ∧ s.mints = S₁.empty)

def reachable (sx: SX) (s: Γ): Prop :=
  ∃ (init: Γ) (tx: Tx sx init s), validInit init

def concat {sx: SX} {init s' s'': Γ}
(t1: Tx sx init s') (t2: Tx sx s' s''): Tx sx init s'' := match t2 with
  | Tx.empty => t1
  | Tx.dep0 ds rs d => Tx.dep0 ds (concat t1 rs) d
  | Tx.dep ds rs d => Tx.dep ds (concat t1 rs) d
  | Tx.red ds rs r => Tx.red ds (concat t1 rs) r
  | Tx.swap ds rs sw => Tx.swap ds (concat t1 rs) sw

/-
Proof that
m ∈ (Trace c s).Γ.amms.map.supp → supply m > 0

by induction
empty (base case): hypothesis is a contradiction
dep0: trivial by cases on the deposited tokens:
      if the pair is the same, then the supply is positive.
      if the pair isn't the same, the supply is the same as
      before and we can use IH.

dep: same as dep0.

swap: use IH.
      swaps don't change minted token supplies
-/

/- If a state is reachable and an AMM has been initialized in it,
   then the supply of the AMM's minted token is greater than zero. -/
theorem AMMimpMintSupply (r: reachable sx s)
  (h: s.amms.init t0 t1): 0 < s.mints.supply t0 t1 := by

  -- Obtain the initial state and the sequence of transactions
  -- that lead to this reachable state
  have ⟨init, tx, ⟨init_amms, init_accs⟩⟩ := r

  -- By induction on the sequence of transactions
  induction tx with

  -- Contradiction in the empty case:
  -- there cannot be an initialized AMM in the empty AMM Set.
  | empty =>
      exfalso
      simp [Sₐ.init, Sₐ.empty, init_amms] at h

  -- Creation of AMM case: trivial by
  -- cases on the created tokens t0' t1'.
  | @dep0 t0' t1' a r0 r1 sprev tail d ih =>
    apply @Decidable.byCases (diffmint t0' t1' t0 t1)

    -- If their minted token is different, then by definition of
    -- Deposit0, the minted supply remains unchanged.
    -- Then, use the induction hypothesis.
    . intro diff;
      simp [diff] at h
      simp [Deposit0.apply, diff]
      have re: reachable sx sprev := by
        exists init; exists tail
      exact ih re h

    -- If their minted token is the same, then we just incremented
    -- the supply, and since it is non-negative, it must be positive.
    . intro same
      rw [not_diffmint_iff_samemint _ _ _ _ d.hdif] at same
      rw [← S₁.supply_samepair _ _ _ _ _ same]
      simp [Deposit0.apply]
      right
      exact r0.zero_lt_toNNReal

  -- Deposit to liquidity pool case: by cases
  -- on the deposited tokens t0' t1'. Similar to Creation.
  | @dep a t0' t1' v0 sprev tail d ih =>
      simp at h
      have re: reachable sx sprev := by
        exists init; exists tail

      -- If the minted token is different, then the supply
      -- remains unchanged. Use induction hypothesis.
      rcases Decidable.em (diffmint t0' t1' t0 t1) with diffmi|samemi
      . simp [diffmi, ih re h]

      -- If the minted token is the same, then we just
      -- incremented the supply.
      . rw [not_diffmint_iff_samemint _ _ _ _ d.exi.dif] at samemi
        rcases samemi with ⟨a,b⟩|⟨a,b⟩
        . simp [a, b, d.v.zero_lt_toNNReal]
        . rw [S₁.supply_reorder _ t0 t1]
          simp [a, b, d.v.zero_lt_toNNReal]


  -- Redeem: by cases on the redeemed tokens.
  | @red a t0' t1' v sprev tail d ih =>
      simp at h
      simp [Γ.mintsupply]
      have re: reachable sx sprev := by
        exists init; exists tail

      rcases Decidable.em (diffmint t0' t1' t0 t1) with diffmi|samemi

      -- If the minted token is different,
      -- then the supply remains unchanged. Use IH.
      . simp [diffmi, ih re h]

      -- If the minted token is the same,
      -- we subtracted from the supply, but the
      -- subtracted value is less than the total supply,
      -- by definition of a valid redeem transaction.
      . rw [not_diffmint_iff_samemint _ _ _ _ d.exi.dif] at samemi
        rcases samemi with ⟨a,b⟩|⟨a,b⟩
        . simp [← a, ← b, d.nodrain_toNNReal]

        . have nodrain' := d.nodrain_toNNReal
          rw [S₁.supply_reorder _ t0 t1]
          simp_rw [← a, ← b] at nodrain' ⊢
          simp [nodrain']

  -- The swap case is trivial since minted wallets are
  -- unchanged by swap transactions.
  | swap sprev tail sw ih =>
      simp at h
      have re: reachable sx sprev := by
        exists init; exists tail
      exact ih re h
