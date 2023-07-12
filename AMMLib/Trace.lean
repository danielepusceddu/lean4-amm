import AMMLib.Deposit
import AMMLib.Redeem
import AMMLib.State
import AMMLib.Tokens
import AMMLib.Swap.Basic
import AMMLib.Networth

/- Tx c init s is the type of all possible sequences of transactions
  that would result in s, starting from Γ init and using configuration c -/
inductive Tx (sx: SX) (init: Γ): Γ → Type where
  | empty: Tx sx init init

  | dep0 (s': Γ) (rs: Tx sx init s') (d: Deposit0 s'): 
      Tx sx init d.apply
  
  | dep (s': Γ) (rs: Tx sx init s') (d: Deposit s' a t0 t1 v0):
      Tx sx init d.apply

  | red (s': Γ) (rs: Tx sx init s') (r: Redeem s' a t0 t1 v0):
      Tx sx init r.apply

  | swap (s': Γ) (rs: Tx sx init s') 
         (sw: Swap sx s' a t0 t1 v0):
      Tx sx init sw.apply

def reachableInit (s: Γ): Prop :=
  (s.amms = Sₐ.empty ∧ s.mints = S₁.empty)

def reachable (sx: SX) (s: Γ): Prop :=
  ∃ (init: Γ) (tx: Tx sx init s), reachableInit init

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
theorem Γ.mintsupply_samepair (s: Γ) (t0 t1 t0' t1': T) (samepair: samemint t0 t1 t0' t1'):
  s.mintsupply t0 t1 = s.mintsupply t0' t1' := by sorry

theorem AMMimpSupplyProp
{sx: SX} {s: Γ} (r: reachable sx s) {t0 t1: T}
(h: s.amms.init t0 t1)
: 0 < s.mintsupply t0 t1 := by
  have ⟨init, tx, ⟨init_amms, init_accs⟩⟩ := r
  induction tx with
  | empty => 
      exfalso
      simp [Sₐ.init, Sₐ.empty, init_amms] at h

  | dep0 sprev tail d ih =>
    apply @Decidable.byCases (diffmint d.t0 d.t1 t0 t1)
    . intro diff;
      simp [diff] at h
      simp [Deposit0.apply, Γ.mintsupply, diff]
      have re: reachable sx sprev := by
        exists init; exists tail
      exact ih re h
    
    . intro same
      rw [not_diffmint_iff_samemint _ _ _ _ d.hdif] at same
      rw [← Γ.mintsupply_samepair _ _ _ _ _ same]
      simp [Γ.mintsupply, Deposit0.apply]
      right
      exact d.r0.zero_lt_toNNReal
  
  | @dep a t0' t1' v0 sprev tail d ih =>
      simp at h
      have re: reachable sx sprev := by
        exists init; exists tail

      unfold Γ.mintsupply
      rcases Decidable.em (diffmint t0' t1' t0 t1) with diffmi|samemi
      . simp [diffmi, ih re h]; exact ih re h
      . rw [not_diffmint_iff_samemint _ _ _ _ d.exi.dif] at samemi
        rcases samemi with ⟨a,b⟩|⟨a,b⟩
        . simp [a, b, d.v.zero_lt_toNNReal]
        . rw [S₁.supply_reorder _ t0 t1]
          simp [a, b, d.v.zero_lt_toNNReal]

  | @red a t0' t1' v0 sprev tail d ih =>
      simp at h
      simp [Γ.mintsupply]
      have re: reachable sx sprev := by
        exists init; exists tail

      rcases Decidable.em (diffmint t0' t1' t0 t1) with diffmi|samemi
      . simp [diffmi, ih re h]; exact ih re h
      . rw [not_diffmint_iff_samemint _ _ _ _ d.exi.dif] at samemi
        rcases samemi with ⟨a,b⟩|⟨a,b⟩
        . have nodrain': v0 < sprev.mints.supply t0 t1 := by
            have nodrain := d.nodrain
            rw [← PReal.toNNReal_lt_toNNReal_iff] at nodrain
            simp [a,b] at nodrain
            exact nodrain
          simp [a, b, nodrain']

        . have nodrain': v0 < sprev.mints.supply t1 t0 := by
            have bruh := d.nodrain
            rw [← PReal.toNNReal_lt_toNNReal_iff] at bruh
            simp [a,b] at bruh
            exact bruh
          rw [S₁.supply_reorder _ t0 t1]
          simp [a, b, nodrain']
  
  | swap sprev tail sw ih =>
      rw [sw.mintsupply]
      simp at h
      have re: reachable sx sprev := by
        exists init; exists tail
      exact ih re h
