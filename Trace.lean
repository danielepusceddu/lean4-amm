import «Deposit»
import «State»
import «Tokens»
import «Swap»

inductive Trace (c: Config): State → Type where
  | empty (accs: AccountSet) 
    (h: ∀(a: Account) (m: MintedTok), accs a m = 0): 
      Trace c ⟨accs, AMMSet.empty⟩

  | dep0 (s: State) (rs: Trace c s) (d: Deposit0.Valid s): 
      Trace c (Deposit0.apply d)

  | swap (s: State) (rs: Trace c s) (sw: Swap.Valid c s):
      Trace c (Swap.apply sw)

/-
Proof that 
m ∈ (Trace c s).state.amms.map.supp → supply m > 0

by induction
empty (base case): hypothesis is a contradiction
dep0: trivial
swap: use IH. 
      swaps don't change minted token supplies
-/
theorem AMMimpSupply 
(t: Trace c s) (t0 t1: AtomicTok) (h: s.amms.f t0 t1 ≠ 0)
: 0 < s.supply (AtomicTok.toMint (AMMSet.exists_imp_dif h)) := by
  induction t with
  | empty accs _ => 
    exfalso
    simp [AMMSet.empty] at h

  | dep0 s' _ d ih =>
    apply @Decidable.byCases ((AtomicTok.toMint (AMMSet.exists_imp_dif h))=(AtomicTok.toMint d.hdif))
    . intro eq; rw [eq]
      simp [Deposit0.apply, State.supply]
      rw [AccountSet.supply_addb_same (((s'.accs.subb d.a d.t0 d.r0).subb d.a d.t1 d.r1)) (AtomicTok.toMint d.hdif) d.a d.r0]
      apply NNReal.neq_zero_imp_gt
      exact NNReal.pos_imp_add_pos d.r0 _ (d.r0.coe_nnreal_pos)

    . intro neq
      simp [neq]
      simp [AtomicTok.toMint_diff neq] at h
      exact ih h
  
  | swap s' _ sw ih =>
    rw [Swap.mintedSupply]
    have h' := Swap.amm_in_apply h
    exact ih h'
