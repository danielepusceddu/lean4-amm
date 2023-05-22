import «Deposit»
import «State»
import «Tokens»
import «Swap»

/- Tx c init s is the type of all possible sequences of transactions
  that would result in s, starting from state init and using configuration c -/
inductive Tx (c: Config) (init: State): State → Type where
  | empty: Tx c init init

  | dep0 (s': State) (rs: Tx c init s') (d: Deposit0.Valid s'): 
      Tx c init (Deposit0.apply d)

  | swap (s': State) (rs: Tx c init s') (sw: Swap.Valid c s'):
      Tx c init (Swap.apply sw)

def reachableInit (s: State): Prop :=
  (s.amms = AMMSet.empty ∧ ∀ (a: Account) (m: MintedTok), s.accs a m = 0)

def reachable (c: Config) (s: State): Prop :=
  ∃ (init: State) (tx: Tx c init s), reachableInit init

structure Reachable (c: Config) (s: State) where
  init: State
  tx: Tx c init s
  init_amms: init.amms = AMMSet.empty
  init_accs: ∀ (a: Account) (m: MintedTok), init.accs a m = 0

def concat {c: Config} {init s' s'': State} 
(t1: Tx c init s') (t2: Tx c s' s''): Tx c init s'' := match t2 with
  | Tx.empty => t1
  | Tx.dep0 ds rs d => Tx.dep0 ds (concat t1 rs) d
  | Tx.swap ds rs sw => Tx.swap ds (concat t1 rs) sw

/-
Proof that 
m ∈ (Trace c s).state.amms.map.supp → supply m > 0

by induction
empty (base case): hypothesis is a contradiction
dep0: trivial by cases on the deposited tokens:
      if the pair is the same, then the supply is positive.
      if the pair isn't the same, the supply is the same as
      before and we can use IH.
swap: use IH. 
      swaps don't change minted token supplies
-/

theorem AMMimpSupplyProp
{c: Config} {s: State} (r: reachable c s) {t0 t1: AtomicTok}
(h: s.amms.f t0 t1 ≠ 0)
: 0 < s.supply (AtomicTok.toMint (AMMSet.exists_imp_dif h)) := by
  have ⟨init, tx, ⟨init_amms, init_accs⟩⟩ := r
  induction tx with
  | empty => 
      exfalso
      simp [init_amms, AMMSet.empty] at h

  | dep0 sprev tail d ih =>
    apply @Decidable.byCases ((AtomicTok.toMint (AMMSet.exists_imp_dif h))=(AtomicTok.toMint d.hdif))
    . intro eq; rw [eq]
      simp [Deposit0.apply, State.supply]
      rw [AccountSet.supply_addb_same (((sprev.accs.subb d.a d.t0 d.r0).subb d.a d.t1 d.r1)) (AtomicTok.toMint d.hdif) d.a d.r0]
      apply NNReal.neq_zero_imp_gt
      exact NNReal.pos_imp_add_pos d.r0 _ (d.r0.coe_nnreal_pos)
    
    . intro neq
      simp [neq]
      simp [AtomicTok.toMint_diff neq] at h
      have re: reachable c sprev := by
        exists init; exists tail
      exact ih re h
  
  | swap sprev tail sw ih =>
      rw [Swap.mintedSupply]
      have h' := Swap.amm_in_apply h
      have re: reachable c sprev := by
        exists init; exists tail
      exact ih re h'
